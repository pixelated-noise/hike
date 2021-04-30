(ns sherpa.core
  (:require [clojure.spec.alpha :as s]))

;;; Low-level transformations
(defn- split [{:keys [index count]}]
  (fn [n & _] (if (< n index) n (+ n count))))

(defn- dead-end [{:keys [index count]}]
  ;; `n` passes if outside the non-inclusive (`min-pass`, `max-pass`)
  ;; interval, otherwise `nil` is normally returned.
  (let [min-pass (dec index)
        max-pass (+ index count)]
    ;; overcome the dead-end by following the specified `bypass` direction
    (fn [n & [bypass]]
      (cond (<= n min-pass) n
            (< n max-pass)  (get {:min min-pass
                                  :max index}
                                 bypass)
            :else           (- n count)))))

(defn- cross [{:keys [index count offset] :as tf}]
  (assert (pos? offset))
  ;; `n` passes through if outside the non-inclusive (`min-pass`, `max-pass`)
  ;; interval, `cross-index` marks the start of the complementary cell group.
  (let [min-pass    (dec index)
        cross-index (+ index count)
        max-pass    (+ cross-index offset)]
    (fn [n & _]
      (cond (or (<= n min-pass) (<= max-pass n)) n
            (<= index n (dec cross-index))       (+ n offset)
            :else                                (- n count)))))

;;; Bidirectional transformations
(defn- normalize-move [{:keys [index count offset] :as tf}]
  (if (pos? offset) tf
      {:index  (+ index offset)
       :count  (- offset)
       :offset count}))

(defn- make-transformation [{:keys [action] :as op}]
  (condp = action
    :insert {:to-graph (dead-end op) :to-grid (split op)}
    :delete {:to-graph (split op) :to-grid (dead-end op)}
    ;; normalize the `move` (ensuring a positive `offset`) to enable swapping
    ;; of `count` with `offset` for the `to-graph` transformation
    :move   (let [{:keys [count offset] :as op} (normalize-move op)]
              {:to-graph (cross (merge op {:count  offset
                                           :offset count}))
               :to-grid  (cross op)})))

;;; A stack of transformations between layouts. Every position in a layout is
;;; uniquely mapped to a graph node. A grid->graph result contains the exit
;;; layout, which is the entry point for the graph->grid direction.
(defn- make-transformation-stack [] [])

(defn- set-status [tf-stack base-layout status]
  (assoc-in tf-stack [base-layout :active] status))

(defn- disable [tf-stack base-layout]
  (set-status tf-stack base-layout false))

(defn- enable [tf-stack base-layout]
  (set-status tf-stack base-layout true))

(defn- push [tf-stack op]
  (->> {:operation op :active true}
       (merge (make-transformation op))
       (conj tf-stack)))

(defn- grid->graph [tf-stack pos]
  (reduce (fn [[layout pos] {:keys [active to-graph]}]
            (if-not active
              ;; `dec` used for tracking the layout regardless of status
              [(dec layout) pos]
              (if-let [to-pos (to-graph pos)]
                [(dec layout) to-pos]
                (reduced [layout pos]))))
          [(count tf-stack) pos]
          (rseq tf-stack)))

(defn- graph->grid
  ([tf-stack node] (graph->grid tf-stack node nil))
  ([tf-stack [layout pos :as node] bypass]
   (letfn [(active? [layout]
             (or (zero? layout)
                 (:active (get tf-stack (dec layout)))))
           (to-active [[layout pos :as node]]
             (->> (subvec tf-stack 0 layout)
                  rseq
                  (take-while (comp not :active))
                  (reduce (fn [[layout pos] {:keys [to-graph]}]
                            [(dec layout) (to-graph pos bypass)])
                          node)))
           (to-grid [[layout pos]]
             (->> (subvec tf-stack layout)
                  (filter :active)
                  (reduce (fn [pos {:keys [active to-grid]}]
                            (or (to-grid pos bypass)
                                (reduced nil)))
                          pos)))]
     (cond (active? layout) (to-grid node)
           bypass           (-> node to-active to-grid)))))

;;; Spec provided here as an overview
(s/def ::id (s/and integer? (complement neg?)))

(s/def ::node
  (s/keys :req-un [::sheet ::row-layout ::row-pos ::col-layout ::col-pos]))
(s/def ::sheet ::id)
(s/def ::row-layout ::id)
(s/def ::row-pos ::id)
(s/def ::col-layout ::id)
(s/def ::col-pos ::id)

(s/def ::slice (s/keys :req-un [::start ::end]))
(s/def ::start ::node)
(s/def ::end ::node)

(s/def ::cell (s/keys :req-un [::sheet ::row ::col]))
(s/def ::row ::id)
(s/def ::col ::id)

(s/def ::graph-map (s/keys :req-un [::row-stack ::col-stack ::trail]))
(s/def ::transformation-stack (s/coll-of ::transformation))
(s/def ::row-stack ::transformation-stack)
(s/def ::col-stack ::transformation-stack)
(s/def ::trail (s/keys :req-un [::op-pointers ::last-active]))
(s/def ::last-active integer?)
(s/def ::op-pointers (s/coll-of ::op-pointer))
(s/def ::op-pointer (s/cat :target #{:row-stack :col-stack}
                           :index ::id))

(s/def ::transformation
  (s/keys :req-un [::to-grid ::to-graph ::operation ::active]))
(s/def ::to-grid fn?)
(s/def ::to-graph fn?)
(s/def ::operation (s/keys :req-un [::action ::index ::count]
                           :opt-un [::offset]))
(s/def ::action #{:insert :delete :move})
(s/def ::index ::id)
(s/def ::count ::id)
(s/def ::offset integer?)
(s/def ::active boolean?)

;;; Encoding/decoding via byte-interleaving pairing functions.

;;; The `java.util.Arrays/copyOf` method won't do, since we need low padding
(defn- zero-pad [ba new-size]
  ;; this being private, it's safe to assume that `new-size` > `(alength ba)`
  (let [old-size (alength ba)
        bba      (byte-array new-size (byte 0))]
    ;; (Object src, int srcPos, Object dest, int destPos, int length)
    (System/arraycopy ba 0 bba (- new-size old-size) old-size)
    bba))

(defn- pair [[m n]]
  (let [m-ba   (-> m biginteger .toByteArray)
        n-ba   (-> n biginteger .toByteArray)
        m-size (alength m-ba)
        n-size (alength n-ba)]
    (->> (cond (< m-size n-size) [(zero-pad m-ba n-size) n-ba]
               (= m-size n-size) [m-ba n-ba]
               (> m-size n-size) [m-ba (zero-pad n-ba m-size)])
         (apply interleave)
         byte-array
         biginteger)))

(defn- unpair [p]
  (let [ba (->> p biginteger .toByteArray)
        ;; pad byte-array with zeros to an even total length
        bseq (if (odd? (alength ba))
               (concat [0 0 0] ba)
               (concat [0 0] ba))]
    (map (comp biginteger byte-array)
         [(take-nth 2 bseq) (take-nth 2 (drop 1 bseq))])))

(defn- encode [{:keys [sheet row-layout row-pos col-layout col-pos]}]
  "Encodes the supplied nonnegative `coordinates` into a natural number."
  (pair [sheet (pair [(pair [row-layout row-pos])
                      (pair [col-layout col-pos])])]))

(defn- decode [code]
  "Decodes the coordinates from the supplied nonnegative `code`."
  (let [[sheet row-col-code] (unpair code)
        [row-code col-code]  (unpair row-col-code)
        [row-layout row-pos] (unpair row-code)
        [col-layout col-pos] (unpair col-code)]
    {:sheet      sheet
     :row-layout row-layout
     :row-pos    row-pos
     :col-layout col-layout
     :col-pos    col-pos}))

;;; Conversion between nodes and cells
(defn- node->cell
  ([node graph-map]
   (node->cell node graph-map nil))
  ([{:keys [sheet row-layout row-pos col-layout col-pos]}
    {:keys [row-stack col-stack]}
    bypass]
   (when-let [row (graph->grid row-stack [row-layout row-pos] bypass)]
     (when-let [col (graph->grid col-stack [col-layout col-pos] bypass)]
       {:sheet sheet :row row :col col}))))

(defn- slice->cells [{:keys [start end]} graph-map]
  (let [{sr :row sc :col ss :sheet} (node->cell start graph-map :max)
        {er :row ec :col es :sheet} (node->cell end graph-map :min)]
    (assert (= es ss))
    (for [row (range sr (inc er))
          col (range sc (inc ec))]
      {:sheet es :row row :col col})))

(defn- cell->node [{:keys [sheet row col]} {:keys [row-stack col-stack]}]
  (let [[row-layout row-pos] (grid->graph row-stack row)
        [col-layout col-pos] (grid->graph col-stack col)]
    {:sheet      sheet
     :row-layout row-layout
     :row-pos    row-pos
     :col-layout col-layout
     :col-pos    col-pos}))

;;; Public API
(defn node-id->cell
  "Returns the cell for `node` according to the `graph-map` in effect,
  `nil` if not visible. Can be used for slice edges by specifycing the
  appropriate `bypass` direction."
  [node-id graph-map]
  (-> node-id decode (node->cell graph-map)))

(defn slice-ids->cells
  "Returns the `slice`'s cells according to `graph-map` in effect."
  [{:keys [start end]} graph-map]
  (slice->cells {:start (decode start) :end (decode end)} graph-map))

(defn cell->node-id [cell graph-map]
  "Returns the node for `cell` according to the `graph-map` in effect."
  (-> cell (cell->node graph-map) encode))

(defn make []
  {:row-stack (make-transformation-stack)
   :col-stack (make-transformation-stack)
   :trail     {:op-pointers []
               :last-active -1}})

(defn- truncate-undone [{{:keys [op-pointers last-active]} :trail
                         :as                               graph-map}]
  (assoc-in graph-map
            [:trail :op-pointers]
            (subvec op-pointers 0 (inc last-active))))

(defn- operate [graph-map target-stack operation]
  (let [target-count (count (get graph-map target-stack))]
    (-> graph-map
        truncate-undone
        (update target-stack push operation)
        (update-in [:trail :op-pointers]
                   conj
                   [target-stack target-count])
        (update-in [:trail :last-active] inc))))

(defn insert-rows [graph-map index count]
  (operate graph-map :row-stack {:action :insert
                                 :index  index
                                 :count  count}))

(defn move-rows [graph-map index count offset]
  (operate graph-map :row-stack {:action :move
                                 :index  index
                                 :count  count
                                 :offset offset}))

(defn delete-rows [graph-map index count]
  (operate graph-map :row-stack {:action :delete
                                 :index  index
                                 :count  count}))

(defn insert-columns [graph-map index count]
  (operate graph-map :col-stack {:action :insert
                                 :index  index
                                 :count  count}))

(defn move-columns [graph-map index count offset]
  (operate graph-map :col-stack {:action :move
                                 :index  index
                                 :count  count
                                 :offset offset}))

(defn delete-columns [graph-map index count]
  (operate graph-map :col-stack {:action :delete
                                 :index  index
                                 :count  count}))

(defn undo [{{:keys [op-pointers last-active]} :trail
             :as                               graph-map}]
  ;; check that there is some operation to undo
  (if (neg? last-active) graph-map
      (let [[target-stack index] (get op-pointers last-active)]
        (-> graph-map
            (update target-stack disable index)
            (update-in [:trail :last-active] dec)))))

(defn redo [{{:keys [last-active op-pointers]} :trail
             :as                               graph-map}]
  ;; get the operation *after* `last-active`
  (if-let [[target-stack index] (get op-pointers (inc last-active))]
    (-> graph-map
        (update target-stack enable index)
        (update-in [:trail :last-active] inc))
    graph-map))
