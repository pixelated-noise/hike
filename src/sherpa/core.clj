(ns sherpa.core
  (:require [clojure.spec.alpha :as s]
            [clojure.math.combinatorics :as comb]))

;;; Low-level constructor for position transformation
(s/def ::nat (s/and integer? (complement neg?)))
(s/def ::position ::nat)

(s/def ::action #{:insert :remove :move})
(s/def ::index ::nat)
(s/def ::count ::nat)
(s/def ::offset integer?)

(defmulti ^:private operation :action)
(defmethod operation :insert [_]
  (s/keys :req-un [::action ::index ::count]))
(defmethod operation :remove [_]
  (s/keys :req-un [::action ::index ::count]))
(defmethod operation :move [_]
  (s/keys :req-un [::action ::index ::count ::offset]))
(s/def ::operation (s/multi-spec operation :action))

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

(defn- cross [{:keys [index count offset]}]
  (s/assert ::nat offset)
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
(defn- normalize-move [{:keys [index count offset] :as op}]
  (if (neg? offset)
    {:index  (+ index offset)
     :count  (- offset)
     :offset count}
    op))

(s/def ::to-grid fn?)
(s/def ::to-graph fn?)
(s/def ::active boolean?)
(s/def ::transformation
  (s/keys :req-un [::to-grid ::to-graph ::active]
          :opt-un [::operation]))

(defn- make-transformation [{:keys [action] :as op}]
  (-> (condp = action
        :insert {:to-graph (dead-end op) :to-grid (split op)}
        :remove {:to-graph (split op) :to-grid (dead-end op)}
        ;; normalize the `move` (ensuring a positive `offset`) to enable
        ;; swapping of `count` with `offset` for the `to-graph` transformation
        :move   (let [{:keys [count offset] :as op} (normalize-move op)]
                  {:to-graph (cross (merge op {:count  offset
                                               :offset count}))
                   :to-grid  (cross op)}))
      (assoc :active true :operation op)))

(s/fdef make-transformation
  :args (s/cat :operation ::operation)
  :ret ::transformation)

;;; Transformation stacks
(s/def ::transformation-stack (s/coll-of ::transformation))
(defn- make-transformation-stack [] [])
(defn- push [tf-stack op] (conj tf-stack (make-transformation op)))
(defn- disable [tf-stack tf-id] (assoc-in tf-stack [tf-id :active] false))
(defn- enable [tf-stack tf-id] (assoc-in tf-stack [tf-id :active] true))

;;; Threading through the stack
(s/def ::layout ::nat)
;; A coordinate along a dimension specifies both the position and layout
(s/def ::coordinate (s/tuple ::nat ::nat))
(s/def ::bypass (s/nilable #{:min :max}))

(defn- to-graph [tf-stack pos]
  (reduce (fn [[layout pos] {:keys [active to-graph]}]
            (if-not active
              ;; `dec` used for tracking the layout regardless of status
              [(dec layout) pos]
              (if-let [to-pos (to-graph pos)]
                [(dec layout) to-pos]
                (reduced [layout pos]))))
          [(count tf-stack) pos]
          (rseq tf-stack)))

(s/fdef to-graph
  :args (s/cat :tf-stack ::transformation-stack
               :pos ::position)
  :ret ::coordinate)

(defn- to-grid
  ([tf-stack origin] (to-grid tf-stack origin nil))
  ([tf-stack [layout pos :as origin] bypass]
   (letfn [(active? [layout]
             (or (zero? layout)
                 (:active (get tf-stack (dec layout)))))
           (to-active [[layout pos :as origin]]
             (transduce (take-while (complement :active))
                        (completing (fn [[layout pos] {:keys [to-graph]}]
                                      [(dec layout) (to-graph pos bypass)]))
                        origin
                        (rseq (subvec tf-stack 0 layout))))
           (to-grid [[layout pos]]
             (transduce (filter :active)
                        (completing (fn [pos {:keys [active to-grid]}]
                                      (or (to-grid pos bypass)
                                          (reduced nil))))
                        pos
                        (subvec tf-stack layout)))]
     (cond (active? layout) (to-grid origin)
           bypass           (-> origin to-active to-grid)))))

(s/fdef to-grid
  :args (s/cat :tf-stack ::transformation-stack
               :origin ::coordinate
               :bypass (s/? ::bypass))
  :ret (s/nilable ::position))

;;; Multidimensional chart
(s/def ::transformations (s/coll-of ::transformation-stack))
(s/def ::dimension->index ifn?)
(s/def ::operation-pointer (s/tuple ::nat ::nat))
(s/def ::operation-pointers (s/coll-of ::operation-pointer))
(s/def ::last-active (s/or :none #{-1} :id ::nat))
(s/def ::trail (s/keys :req-un [::operation-pointers ::last-active]))
(s/def ::dimensions (s/coll-of keyword?))
(s/def ::chart (s/keys :req-un [::transformations ::dimension->index ::trail
                                ::encoder ::decoder]
                       :opt-un [::dimensions]))

(defn make-chart
  "Constructs a multi-dimensional chart. If `dimension-names` are supplied,
  dimensions are named, otherwise anonymous. Iff anonymous, their number is
  defined by `dimension-count`. The `encoder`/`decoder` functions convert
  nodes to/from identifiers for the graph storage backend (both default to
  `identity`)."
  [{:keys [dimension-names dimension-count encoder decoder]
    :or   {encoder identity decoder identity}}]
  (let [named? (seq dimension-names)]
    (cond-> {:transformations  (vec (repeat (if named?
                                              (count dimension-names)
                                              dimension-count)
                                            (make-transformation-stack)))
             :dimension->index (if named?
                                 (zipmap dimension-names (range))
                                 identity)
             :trail            {:operation-pointers []
                                :last-active        -1}
             :encoder          encoder
             :decoder          decoder}
      named? (assoc :dimensions dimension-names))))

(s/fdef make-chart
  :args (s/cat :chart-options
               (s/keys :req-un [(or ::dimension-names ::dimension-count)]
                       :opt-un [::encoder ::decoder]))
  :ret ::chart)

;;; A cell is specified by its coordinates
(s/def ::cell (s/coll-of ::coordinate))
(s/def ::cell-position (s/coll-of ::position))

(defn cell->node [cell {:keys [transformations encoder] :as chart}]
  "Returns the node for `cell` according to `chart`."
  (let [cell->origin (partial map to-graph transformations)]
    (-> cell cell->origin encoder)))

(defn- origin->cell
  ([origin chart]
   (origin->cell origin chart nil))
  ([origin {:keys [transformations]} bypass]
   (reduce (fn [cell-position [coordinate tf-stack]]
             (if-let [position (to-grid tf-stack coordinate bypass)]
               (conj cell-position position)
               (reduced nil)))
           []
           (map vector origin transformations))))

(defn node->cell
  "Returns the cell for `node` according to `chart`, `nil` if not visible."
  [node {:keys [decoder] :as chart}]
  (-> node decoder (origin->cell chart)))

;; A slice is defined by its boundaries
(s/def ::start ::cell)
(s/def ::end ::cell)
(s/def ::slice (s/keys :req-un [::start ::end]))

(defn slice-nodes->cells
  "Returns the `slice`'s cells according to `chart`."
  [{:keys [start end]} {:keys [decoder] :as chart}]
  (let [start  (-> start decoder (origin->cell chart :max))
        end    (-> end decoder (origin->cell chart :min))
        ranges (->> (map inc end) (map range start))]
    (apply comb/cartesian-product ranges)))

(defn- discard-undone
  [{{:keys [operation-pointers last-active]} :trail :as chart}]
  (assoc-in chart
            [:trail :operation-pointers]
            (subvec operation-pointers 0 (inc last-active))))

(defn operate
  "Adds the `operation` on the specified `dimension` to `chart`. For charts with
  named dimensions, `dimension` is a name, otherwise an index. Discards any
  previously undone operations."
  [{:keys [dimension->index transformations] :as chart} dimension operation]
  (let [index    (dimension->index dimension)
        tf-count (count (nth transformations index))]
    (-> chart
        discard-undone
        (update-in [:transformations index] push operation)
        (update-in [:trail :operation-pointers] conj [index tf-count])
        (update-in [:trail :last-active] inc))))

(defn undo
  "Deactivates the last active operation in `chart`, if any."
  [{{:keys [operation-pointers last-active]} :trail :as chart}]
  ;; check that there is some operation to undo
  (if (neg? last-active) chart
      (let [[dim-id tf-id] (get operation-pointers last-active)]
        (-> chart
            (update-in [:transformations dim-id] disable tf-id)
            (update-in [:trail :last-active] dec)))))

(defn redo
  "Reactivates the last deactivated operation in `chart`, if any."
  [{{:keys [last-active operation-pointers]} :trail :as chart}]
  ;; get the operation *after* `last-active`
  (if-let [[dim-id tf-id] (get operation-pointers (inc last-active))]
    (-> chart
        (update-in [:transformations dim-id] enable tf-id)
        (update-in [:trail :last-active] inc))
    chart))
