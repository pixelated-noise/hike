(ns hike.core
  (:require [clojure.spec.alpha :as s]
            [clojure.math.combinatorics :as comb]))

;;; Unidirectional transformers
(s/def ::position integer?)
(s/def ::nat (s/and integer? (complement neg?)))

(s/def ::action keyword?)
(s/def ::index ::position)
(s/def ::count ::nat)
(s/def ::offset integer?)
(defmulti ^:private operation :action)
(defmethod operation :insert [_]
  (s/keys :req-un [::action ::index ::count]))
(defmethod operation :remove [_]
  (s/keys :req-un [::action ::index ::count]))
(defmethod operation :transpose [_]
  (s/keys :req-un [::action ::index ::count ::offset]))
(s/def ::operation (s/multi-spec operation :action))

(defn- split [{:keys [index count]}]
  (fn [pos & _] (if (< pos index) pos (+ pos count))))

(s/def ::bypass (s/nilable #{:min :max}))

(defn- dead-end [{:keys [index count]}]
  ;; `pos` passes if outside the non-inclusive (`min-pass`, `max-pass`)
  ;; interval, otherwise returns `nil`.
  (let [min-pass (dec index)
        max-pass (+ index count)]
    ;; overcome the dead-end by following the specified `bypass` direction
    (fn [pos & [bypass]]
      (cond (<= pos min-pass) pos
            (< pos max-pass)  (get {:min min-pass
                                    :max index}
                                   bypass)
            :else             (- pos count)))))

(defn- cross [{:keys [index count offset]}]
  (s/assert ::nat offset)
  ;; `pos` passes if outside the non-inclusive (`min-pass`, `max-pass`)
  ;; interval, `cross-index` marks the start of the complementary cell group.
  (let [min-pass    (dec index)
        cross-index (+ index count)
        max-pass    (+ cross-index offset)]
    (fn [pos & _]
      (cond (or (<= pos min-pass) (<= max-pass pos)) pos
            (<= index pos (dec cross-index))         (+ pos offset)
            :else                                    (- pos count)))))

;;; Bidirectional transformations
(s/def ::ascend fn?)
(s/def ::descend fn?)
(s/def ::transformers (s/keys :req-un [::ascend ::descend]))
(s/def ::active boolean?)
(s/def ::transformation
  (s/merge ::transformers (s/keys :req-un [::active] :opt-un [::operation])))

(defmulti make-transformers :action)

(s/fdef make-transformers
  :args (s/cat :operation ::operation)
  :ret ::transformers)

(defmethod make-transformers :insert [op]
  {:descend (dead-end op) :ascend (split op)})

(defmethod make-transformers :remove [op]
  {:descend (split op) :ascend (dead-end op)})

(defmethod make-transformers :transpose [{:keys [index count offset] :as op}]
  ;; normalize `transpose` (ensuring a positive `offset`) to enable swapping
  ;; of `count` with `offset` for the `descend` transformation
  (let [{:keys [count offset] :as op} (if-not (neg? offset) op
                                              {:index  (+ index offset)
                                               :count  (- offset)
                                               :offset count})]
    {:descend (cross (merge op {:count offset :offset count}))
     :ascend  (cross op)}))

(defn- make-transformation [op]
  (-> op make-transformers (assoc :active true :operation op)))

(s/fdef make-transformation
  :args (s/cat :operation ::operation)
  :ret ::transformation)

;;; Transformation stacks
(s/def ::transformation-stack (s/coll-of ::transformation))
(defn- make-transformation-stack [] [])
(defn- push [tf-stack op] (conj tf-stack (make-transformation op)))
(defn- disable [tf-stack tf-idx] (assoc-in tf-stack [tf-idx :active] false))
(defn- enable [tf-stack tf-idx] (assoc-in tf-stack [tf-idx :active] true))

;;; Threading through transformation stacks
(s/def ::layout ::nat)
(s/def ::coordinate (s/tuple ::layout ::position))

(defn- descend [tf-stack pos]
  (reduce (fn [[layout pos] {:keys [active descend]}]
            (if-not active
              ;; `dec` used for tracking the layout regardless of status
              [(dec layout) pos]
              (if-let [to-pos (descend pos)]
                [(dec layout) to-pos]
                (reduced [layout pos]))))
          [(count tf-stack) pos]
          (rseq tf-stack)))

(s/fdef descend
  :args (s/cat :tf-stack ::transformation-stack :pos ::position)
  :ret ::coordinate)

(defn- ascend
  ([tf-stack coordinate] (ascend tf-stack coordinate nil))
  ([tf-stack [layout pos :as coordinate] bypass]
   (letfn [(active? [layout]
             (or (zero? layout)
                 (:active (get tf-stack (dec layout)))))
           (to-active [[layout pos :as coordinate]]
             (transduce (take-while (complement :active))
                        (completing (fn [[layout pos] {:keys [descend]}]
                                      [(dec layout) (descend pos bypass)]))
                        coordinate
                        (rseq (subvec tf-stack 0 layout))))
           (to-visible [[layout pos]]
             (transduce (filter :active)
                        (completing (fn [pos {:keys [active ascend]}]
                                      (or (ascend pos bypass)
                                          (reduced nil))))
                        pos
                        (subvec tf-stack layout)))]
     (cond (active? layout) (to-visible coordinate)
           bypass           (-> coordinate to-active to-visible)))))

(s/fdef ascend
  :args (s/cat :tf-stack ::transformation-stack
               :coordinate ::coordinate
               :bypass (s/? ::bypass))
  :ret (s/nilable ::position))

;;; Multidimensional chart
(s/def ::dimensions (s/and (s/coll-of keyword?) (partial apply distinct?)))
(s/def ::dimensionality nat-int?)
(s/def ::tf-stacks (s/coll-of ::transformation-stack))
(s/def ::dim->index ifn?)
(s/def ::dim-index ::nat)
(s/def ::tf-index ::nat)
(s/def ::op-pointers (s/coll-of (s/tuple ::dim-index ::tf-index)))
(s/def ::last-active (s/or :none #{-1} :idx ::nat))
(s/def ::trail (s/keys :req-un [::op-pointers ::last-active]))
(s/def ::encode ifn?)
(s/def ::decode ifn?)
(s/def ::chart (s/keys :req-un [::tf-stacks ::dim->index ::trail
                                ::encode ::decode]
                       :opt-un [::dimensions]))

(defn make-chart
  "Constructs a multi-dimensional chart. If `dimensions` are supplied,
  dimensions are named after them, otherwise anonymous. Iff anonymous, their
  number is defined by `dimensionality`. The `encode`/`decode` functions
  convert cell origins to/from IDs (both default to `identity`)."
  [{:keys [dimensions dimensionality encode decode]
    :or   {encode identity decode identity}}]
  (let [named? (seq dimensions)]
    (cond-> {:tf-stacks  (vec (repeat (if named? (count dimensions)
                                          dimensionality)
                                      (make-transformation-stack)))
             :dim->index (if named? (zipmap dimensions (range)) identity)
             :trail      {:op-pointers [] :last-active -1}
             :encode     encode
             :decode     decode}
      named? (assoc :dimensions dimensions))))

(s/fdef make-chart
  :args (s/cat :chart-options
               (s/keys :req-un [(or ::dimensions ::dimensionality)]
                       :opt-un [::encode ::decode]))
  :ret ::chart)

(s/def ::cell (s/coll-of ::position))
(s/def ::origin (s/coll-of ::coordinate))

(defn cell->id
  "Returns the ID for `cell` according to `chart`."
  [cell {:keys [tf-stacks encode] :as chart}]
  (let [cell->origin (partial map descend tf-stacks)]
    (-> cell cell->origin encode)))

(defn- origin->cell
  ([origin chart]
   (origin->cell origin chart nil))
  ([origin {:keys [tf-stacks]} bypass]
   (reduce (fn [cell-position [coordinate tf-stack]]
             (if-let [position (ascend tf-stack coordinate bypass)]
               (conj cell-position position)
               (reduced nil)))
           []
           (map vector origin tf-stacks))))

(defn id->cell
  "Returns the cell for `id` according to `chart`, `nil` if not visible."
  [id {:keys [decode] :as chart}]
  (-> id decode (origin->cell chart)))

(s/def ::id any?)
(s/def ::start ::id)
(s/def ::end ::id)
(s/def ::slice (s/keys :req-un [::start ::end]))

(defn slice->cells
  "Returns the `slice`'s cells according to `chart`."
  [{:keys [start end]} {:keys [decode] :as chart}]
  (let [start  (-> start decode (origin->cell chart :max))
        end    (-> end decode (origin->cell chart :min))
        ranges (->> (map inc end) (map range start))]
    (apply comb/cartesian-product ranges)))

;;; Operations and undo/redo bookkeeping
(defn- discard-undone
  [{{:keys [op-pointers last-active]} :trail :as chart}]
  (assoc-in chart
            [:trail :op-pointers]
            (subvec op-pointers 0 (inc last-active))))

(defn operate
  "Performs `operation` on the `dimension` in `chart`. For charts with named
  dimensions, `dimension` is a name, otherwise an index. Discards any
  previously undone operations."
  [{:keys [dim->index tf-stacks] :as chart} dimension operation]
  (let [dim-idx  (dim->index dimension)
        tf-count (count (nth tf-stacks dim-idx))]
    (-> chart
        discard-undone
        (update-in [:tf-stacks dim-idx] push operation)
        (update-in [:trail :op-pointers] conj [dim-idx tf-count])
        (update-in [:trail :last-active] inc))))

(defn undo
  "Deactivates the last active operation in `chart`, if any."
  [{{:keys [op-pointers last-active]} :trail :as chart}]
  ;; check that there is some operation to undo
  (if (neg? last-active) chart
      (let [[dim-idx tf-idx] (get op-pointers last-active)]
        (-> chart
            (update-in [:tf-stacks dim-idx] disable tf-idx)
            (update-in [:trail :last-active] dec)))))

(defn redo
  "Reactivates the last deactivated operation in `chart`, if any."
  [{{:keys [last-active op-pointers]} :trail :as chart}]
  ;; get the operation *after* `last-active`
  (if-let [[dim-idx tf-idx] (get op-pointers (inc last-active))]
    (-> chart
        (update-in [:tf-stacks dim-idx] enable tf-idx)
        (update-in [:trail :last-active] inc))
    chart))
