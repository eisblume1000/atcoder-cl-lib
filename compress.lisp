;;;; compress.lisp — 重複除去・値ごとの個数・座標圧縮
;;;; https://github.com/eisblume1000/atcoder-cl-lib
;;;;
;;;; 前提: fastio.lisp → radixsort.lisp → bsearch.lisp の後ろに置く。
;;;;
;;;; 対応する配列: (simple-array fixnum (*)) / u32 / i32 の 1 次元配列。
;;;;               同じ関数名のまま、中で型ごとの専用コードに切り替わる。
;;;;
;;;; ════════════════════════════════════════════════════════════════
;;;; (dedup-sorted arr &optional start end) → 新しい end
;;;; ════════════════════════════════════════════════════════════════
;;;;   ソート済みの arr[start..end) から重複を取り除き、前に詰める(その場で書き換え)。
;;;;   返り値は「重複を除いた範囲の終わり」。arr[start..返り値) が結果。
;;;;   それより後ろの要素は残骸なので使わないこと。
;;;;
;;;;   例:
;;;;     a = #(1 1 3 3 3 7)
;;;;     (dedup-sorted a)  → 3      ; a は #(1 3 7 . . .) になる
;;;;
;;;;   使いどころ:
;;;;     - 異なる値の個数を数える
;;;;         (radix-sort-u32 a)
;;;;         (dedup-sorted a)                  ; → 異なる値の個数(start=0 のとき)
;;;;     - 1-indexed の配列なら start = 1。返り値 e に対して個数は (- e 1)
;;;;
;;;; ════════════════════════════════════════════════════════════════
;;;; (dedup-count arr &optional start end) → (values vals counts m)
;;;; ════════════════════════════════════════════════════════════════
;;;;   ソート済みの arr[start..end) を「異なる値」と「その値の個数」に分ける。
;;;;   arr は書き換えない。
;;;;     vals   : 異なる値を昇順に並べた配列(arr と同じ要素型、長さ m)
;;;;     counts : vals[j] が何個あったか((simple-array fixnum (*))、長さ m)
;;;;     m      : 異なる値の個数
;;;;
;;;;   例:
;;;;     a = #(1 1 2 5 5 5)
;;;;     (dedup-count a)  → #(1 2 5), #(2 1 3), 3
;;;;
;;;;   使いどころ:
;;;;     - 値ごとの出現回数(度数分布)。最頻値、同じ値のペアの数など
;;;;         (multiple-value-bind (vals counts m) (dedup-count a)
;;;;           ;; 同じ値を 2 つ選ぶ組の数 = Σ c(c-1)/2
;;;;           (loop for j below m sum (let ((c (aref counts j))) (ash (* c (1- c)) -1))))
;;;;     - ランレングス圧縮(ソート済みとは限らない列でも、隣り合う同じ値をまとめるだけなら使える)
;;;;
;;;; ════════════════════════════════════════════════════════════════
;;;; (compress arr &optional start end) → (values ids vals m)
;;;; ════════════════════════════════════════════════════════════════
;;;;   座標圧縮。arr[start..end) の各値を「小さい方から何番目の値か」(0 始まり)に置き換える。
;;;;   arr はソート済みでなくてよく、書き換えない。
;;;;     ids  : ids[i] = arr[i] の番号((simple-array fixnum (*))、長さ (length arr))
;;;;            arr と同じ添字で使える。範囲外 [0,start) と [end,…) は 0
;;;;     vals : 異なる値を昇順に並べた配列(arr と同じ要素型、長さ m)
;;;;            vals[ids[i]] = arr[i]。番号から元の値に戻すときに使う
;;;;     m    : 異なる値の個数。番号は 0 .. m-1
;;;;
;;;;   例:
;;;;     a = #(100 5 100 30)
;;;;     (compress a)  → ids  #(2 0 2 1)
;;;;                     vals #(5 30 100)
;;;;                     m    3
;;;;
;;;;   使いどころ:
;;;;     - 値が大きい(〜10^9, 10^18)が個数は少ないとき、値を配列の添字として使えるようにする
;;;;       (いもす法・累積和・BIT などで、値の範囲ぶんの配列を作れない場合)
;;;;         (multiple-value-bind (ids vals m) (compress l)   ; 区間の端点を圧縮して
;;;;           (let ((imos (make-array (1+ m) :element-type 'fixnum :initial-element 0)))
;;;;             ...))                                       ; 大きさ m の配列で済む
;;;;     - 値の大小関係だけが重要な問題で、値を 0..m-1 の連番に置き換える
;;;;     - 後から来た値の番号を知りたいときは (lower-bound vals x) で引ける
;;;;
;;;;   計算量: O(N)。radix-argsort で値の順に並べた添字を作り、先頭から順に番号を振る
;;;;
;;;; 前提・制限
;;;;   - dedup-sorted / dedup-count の arr は昇順にソート済みであること(検査しない)。
;;;;   - safety 0 前提で範囲検査はしない。0 <= start <= end <= (length arr) を守ること。

(declaim (optimize (speed 3) (safety 0) (debug 0)))

;; このファイル自身の汎用版の分岐から出る note を抑える(bsearch.lisp と同じ方針)
(declaim (sb-ext:muffle-conditions sb-ext:compiler-note))

;;; ───────── 内部 ─────────

;;; ───────── 重複除去 ─────────

(declaim (inline dedup-sorted))
(defun dedup-sorted (arr &optional (start 0) (end (length arr)))
  (declare (type (simple-array * (*)) arr)
           (type fixnum start end))
  (if (>= start end)
      end
      (%sorted-array-case arr
        (let ((w (1+ start)))                  ; 次に書く位置
          (declare (type fixnum w))
          (loop for r of-type fixnum from (1+ start) below end
                do (let ((v (aref arr r)))
                     ;; 「最後に書いた値」と比べるので、上書きしながら進めても壊れない
                     (when (/= v (aref arr (1- w)))
                       (setf (aref arr w) v)
                       (incf w))))
          w))))

;;; ───────── 値ごとの個数 ─────────

(defun dedup-count (arr &optional (start 0) (end (length arr)))
  (declare (type (simple-array * (*)) arr)
           (type fixnum start end))
  (if (>= start end)
      (values (subseq arr start start)
              (make-array 0 :element-type 'fixnum)
              0)
      (let* ((vals (subseq arr start end))     ; arr と同じ要素型になる
             (counts (make-array (- end start) :element-type 'fixnum :initial-element 0))
             (m 0))
        (declare (type fixnum m)
                 (type (simple-array fixnum (*)) counts))
        (%sorted-array-case vals
          (let ((n (length vals)))
            (declare (type fixnum n))
            (setf (aref counts 0) 1)
            (loop for r of-type fixnum from 1 below n
                  do (let ((v (aref vals r)))
                       (if (= v (aref vals m))
                           (incf (aref counts m))
                           (progn (incf m)
                                  (setf (aref vals m) v
                                        (aref counts m) 1)))))
            (incf m)))
        (values (subseq vals 0 m) (subseq counts 0 m) m))))

;;; ───────── 座標圧縮 ─────────

(defun compress (arr &optional (start 0) (end (length arr)))
  (declare (type (simple-array * (*)) arr)
           (type fixnum start end))
  (let ((ids (make-array (length arr) :element-type 'fixnum :initial-element 0)))
    (declare (type (simple-array fixnum (*)) ids))
    ;; arr の型で 1 回だけ分岐する。分岐の中では arr・vals の型がわかるので、
    ;; 比較や代入が型専用のコードになる。
    (%sorted-array-case arr
      (let* ((perm (radix-argsort arr start end)) ; 1. 値の昇順に並べたときの添字
             (n (length perm))
             (vals (subseq arr start end))        ;    (同じ要素型の作業配列として使う)
             (m 0))
        (declare (type (simple-array fixnum (*)) perm) (type fixnum n m))
        ;; 2. 小さい順に見ていき、前と違う値が来たら新しい番号を振る
        (dotimes (j n)
          (let* ((i (aref perm j))
                 (v (aref arr i)))
            (declare (type fixnum i))
            (when (or (= m 0) (/= v (aref vals (1- m))))
              (setf (aref vals m) v)
              (incf m))
            (setf (aref ids i) (1- m))))
        (values ids (subseq vals 0 m) m)))))

(declaim (sb-ext:unmuffle-conditions sb-ext:compiler-note))
