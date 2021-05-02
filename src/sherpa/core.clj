(ns sherpa.core
  (:require [clojure.spec.alpha :as s]
            [clojure.math.combinatorics :as comb]))

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
(s/def ::layout ::id)
(s/def ::position ::id)

;; A cell is defined by a set of position on each dimension
(s/def ::cell (s/coll-of ::position))

;; A node coordinate also specifies the layout for each dimension
(s/def ::node-coordinate (s/cat :layout ::id :position ::id))
(s/def ::node (s/coll-of ::node-coordinate))

;; A slice is defined by its node boundaries
(s/def ::start ::node)
(s/def ::end ::node)
(s/def ::slice (s/keys :req-un [::start ::end]))

;; Operations and transformations
(s/def ::to-grid fn?)
(s/def ::to-graph fn?)
(s/def ::action #{:insert :delete :move})
(s/def ::index ::id)
(s/def ::count ::id)
(s/def ::offset integer?)
(s/def ::operation (s/keys :req-un [::action ::index ::count]
                           :opt-un [::offset]))
(s/def ::active boolean?)
(s/def ::transformation
  (s/keys :req-un [::to-grid ::to-graph ::operation ::active]))

;; Transformations stack and chart
(s/def ::transformation-stack (s/coll-of ::transformation))
(s/def ::transformations (s/coll-of ::transformation-stack))
(s/def ::op-pointer (s/cat :dimension ::id :index ::id))
(s/def ::op-pointers (s/coll-of ::op-pointer))
(s/def ::last-active (s/or :none #{-1} :id ::id))
(s/def ::trail (s/keys :req-un [::op-pointers ::last-active]))
(s/def ::dimensions (s/coll-of keyword?))
(s/def ::chart (s/keys :req-un [::transformations ::trail
                                ::encoder ::decoder]
                       :opt-un [::dimensions]))

;;; Conversion between nodes and cells
(defn- node->cell
  ([node chart]
   (node->cell node chart nil))
  ([node {:keys [transformations]} bypass]
   (reduce (fn [position [node-coordinate tf-stack]]
             (if-let [pos-coord (graph->grid tf-stack node-coordinate bypass)]
               (conj position pos-coord)
               (reduced nil)))
           []
           (map vector node transformations))))

(defn- slice->cells [{:keys [start end]} chart]
  (let [start  (node->cell start chart :max)
        end    (node->cell end chart :min)
        ranges (->> (map inc end) (map range start))]
    (apply comb/cartesian-product ranges)))

(defn- cell->node [cell {:keys [transformations]}]
  (map grid->graph transformations cell))

;;; Public API
(defn node-id->cell
  "Returns the cell for `node` according to the `chart` in effect,
  `nil` if not visible. Can be used for slice edges by specifycing the
  appropriate `bypass` direction."
  [node-id {:keys [decoder] :as chart}]
  (-> node-id decoder (node->cell chart)))

(defn slice-ids->cells
  "Returns the `slice`'s cells according to `chart` in effect."
  [{:keys [start end]} {:keys [decoder] :as chart}]
  (slice->cells {:start (decoder start) :end (decoder end)} chart))

(defn cell->node-id [cell {:keys [encoder] :as chart}]
  "Returns the node for `cell` according to the `chart` in effect."
  (-> cell (cell->node chart) encoder))

(defn make-chart [{:keys [dimensions dimensionality encoder decoder]
                   :or   {encoder identity decoder identity}}]
  (cond-> {:transformations (vec (repeat (if (seq dimensions)
                                           (count dimensions)
                                           dimensionality)
                                         (make-transformation-stack)))
           :trail           {:op-pointers []
                             :last-active -1}
           :encoder         encoder
           :decoder         decoder}
    dimensions (assoc :dimensions dimensions)))

(defn- truncate-undone [{{:keys [op-pointers last-active]} :trail :as chart}]
  (assoc-in chart
            [:trail :op-pointers]
            (subvec op-pointers 0 (inc last-active))))

(defn operate
  [{:keys [dimensions transformations] :as chart} dimension operation]
  (let [index    (if dimensions
                   (.indexOf dimensions dimension)
                   dimension)
        tf-count (count (nth transformations index))]
    (-> chart
        truncate-undone
        (update-in [:transformations index] push operation)
        (update-in [:trail :op-pointers] conj [index tf-count])
        (update-in [:trail :last-active] inc))))

(defn undo [{{:keys [op-pointers last-active]} :trail :as chart}]
  ;; check that there is some operation to undo
  (if (neg? last-active) chart
      (let [[dim-id tf-id] (get op-pointers last-active)]
        (-> chart
            (update-in [:transformations dim-id] disable tf-id)
            (update-in [:trail :last-active] dec)))))

(defn redo [{{:keys [last-active op-pointers]} :trail :as chart}]
  ;; get the operation *after* `last-active`
  (if-let [[dim-id tf-id] (get op-pointers (inc last-active))]
    (-> chart
        (update-in [:transformations dim-id] enable tf-id)
        (update-in [:trail :last-active] inc))
    chart))
