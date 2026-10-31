;;;; pack.lisp — 2 つの整数を 1 つの fixnum に詰める(ビットパッキング)
;;;; https://github.com/eisblume1000/atcoder-cl-lib
;;;;
;;;; 前提: fastio.lisp → radixsort.lisp の後ろに置く。
;;;;
;;;; なぜ詰めるのか
;;;;   (cost . dest) のようなペアをコンスセルで持つと、要素ごとにメモリを確保し、
;;;;   ソートや比較も遅い。2 数を 1 つの fixnum にまとめれば、fixnum の配列 1 本で済み、
;;;;   基数ソートもそのまま使える。
;;;;
;;;; ════════════════════════════════════════════════════════════════
;;;; (define-pack NAME (HI LO) &key (lo-bits 31) (offset 0))
;;;; ════════════════════════════════════════════════════════════════
;;;;   HI を上位ビット、LO を下位 lo-bits ビットに置く形式を定義し、次の関数を作る。
;;;;     (pack-NAME hi lo)       → 詰めた fixnum
;;;;     (NAME-HI p) (NAME-LO p) → それぞれのフィールドを取り出す
;;;;     (sort-NAME-by-HI arr &optional start end)
;;;;     (sort-NAME-by-LO arr &optional start end)
;;;;                             → そのフィールドだけをキーにして昇順に並べる(片側ソート、安定)
;;;;
;;;;   約束: HI には「優先して並べたいほう」を置く。
;;;;     詰めた値の大小 = (HI, LO) の辞書順 になるので、
;;;;     (radix-sort-fixnum arr) で「HI の昇順、同じ HI なら LO の昇順」に並ぶ。
;;;;
;;;;   offset(下駄): 負の数を扱うときに使う。詰める前に両方に offset を足し、
;;;;     取り出すときに引く。足した後の値が 0 以上なので、大小の順序も保たれる。
;;;;
;;;;   入る範囲(どちらも offset を足した後):
;;;;     0 <= lo + offset < 2^lo-bits
;;;;     0 <= hi + offset < 2^(62 - lo-bits)
;;;;   範囲は検査しない。超えると隣のフィールドや符号を壊すので、制約から必ず確認すること。
;;;;   目安: lo-bits = 31 なら両方とも 0 .. 約 2.1*10^9
;;;;         lo-bits = 20 なら LO は 0 .. 約 10^6、HI は 0 .. 約 4.3*10^12
;;;;
;;;; ── 例 1: グラフの辺 (cost, dest)。ダイクストラ法の優先度付きキューなど ──
;;;;   (define-pack edge (cost dest) :lo-bits 20)     ; 頂点番号 < 2^20 ≒ 10^6
;;;;   (let ((e (pack-edge 500 3)))
;;;;     (edge-cost e)   ; → 500
;;;;     (edge-dest e))  ; → 3
;;;;   詰めた値をそのまま比べれば cost の小さい順になる。
;;;;
;;;; ── 例 2: 負の座標 (x, y)。-10^9 <= x, y <= 10^9 ──
;;;;   (define-pack xy (x y) :lo-bits 31 :offset 1000000000)
;;;;   (let ((p (pack-xy -5 7)))
;;;;     (xy-x p)        ; → -5
;;;;     (xy-y p))       ; → 7
;;;;   (radix-sort-fixnum ps) で x の昇順、同じ x なら y の昇順に並ぶ。
;;;;
;;;; ── 例 3: 区間 (L, R) を R の順に並べる(区間スケジューリングなど) ──
;;;;   (define-pack interval (r l) :lo-bits 31)       ; R を上位に置く
;;;;   (let ((a (make-array n :element-type 'fixnum)))
;;;;     (dotimes (i n)
;;;;       (let* ((l (read-fixnum)) (r (read-fixnum)))  ; 入力は L R の順
;;;;         (setf (aref a i) (pack-interval r l))))
;;;;     (radix-sort-fixnum a)                         ; R の昇順(同じ R なら L の昇順)
;;;;     (loop for p across a
;;;;           do (let ((l (interval-l p)) (r (interval-r p))) ...)))
;;;;   同じ R の中で入力順を保ちたいなら (sort-interval-by-r a) を使う。
;;;;
;;;; ── 片側ソートの使いどころ ──
;;;;   (sort-NAME-by-LO a) は LO だけで並べ、LO が同じ要素は元の順番のまま残す。
;;;;   例: 先に別の基準で並べてある列を、LO で安定に並べ直したいとき。
;;;;   降順が欲しい場合は radixsort.lisp の define-radix-sort を直接使う:
;;;;     (define-radix-sort sort-edge-by-dest-desc :element-type fixnum
;;;;                        :descending t :key-byte (byte 20 0))

(declaim (optimize (speed 3) (safety 0) (debug 0)))

(defmacro define-pack (name (hi lo) &key (lo-bits 31) (offset 0))
  (declare (optimize (speed 1)))           ; マクロ本体(展開処理)の note を抑える
  (unless (typep lo-bits '(integer 1 61))
    (error "define-pack: lo-bits ~S must be an integer in 1..61" lo-bits))
  (unless (typep offset '(integer 0 #.(ash 1 61)))
    (error "define-pack: offset ~S must be a non-negative integer" offset))
  (let* ((hi-bits (- 62 lo-bits))
         (mask (1- (ash 1 lo-bits)))
         (sym (lambda (fmt &rest args)
                (intern (apply #'format nil fmt (mapcar #'symbol-name args)))))
         (pack-fn  (funcall sym "PACK-~A" name))
         (hi-fn    (funcall sym "~A-~A" name hi))
         (lo-fn    (funcall sym "~A-~A" name lo))
         (sort-hi  (funcall sym "SORT-~A-BY-~A" name hi))
         (sort-lo  (funcall sym "SORT-~A-BY-~A" name lo)))
    `(progn
       (declaim (inline ,pack-fn ,hi-fn ,lo-fn))
       (defun ,pack-fn (,hi ,lo)
         (declare (type fixnum ,hi ,lo))
         (logior (ash (the (unsigned-byte ,hi-bits) (+ ,hi ,offset)) ,lo-bits)
                 (the (unsigned-byte ,lo-bits) (+ ,lo ,offset))))
       (defun ,hi-fn (p)
         (declare (type (unsigned-byte 62) p))
         (- (ash p ,(- lo-bits)) ,offset))
       (defun ,lo-fn (p)
         (declare (type (unsigned-byte 62) p))
         (- (logand p ,mask) ,offset))
       (define-radix-sort ,sort-hi :element-type fixnum :key-byte (byte ,hi-bits ,lo-bits))
       (define-radix-sort ,sort-lo :element-type fixnum :key-byte (byte ,lo-bits 0))
       ',name)))
