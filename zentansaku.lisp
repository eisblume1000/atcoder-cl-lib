;;;; zentansaku.lisp — 全探索の型（SBCL 用）
;;;;
;;;; 収録している型
;;;;   1. do-subsets / do-bits-on : bit全探索（2^N 通り）        例: ABC479 C, ABC453 C
;;;;   2. do-tuples               : 重複順列（K^N 通り）          例: 3色塗り分け、各要素に3択
;;;;   3. next-permutation        : 辞書順で次の順列（C++ の std::next_permutation 相当）
;;;;      do-permutations         : 順列全探索（N! 通り）          例: ABC468 C
;;;;   4. do-combinations         : 組合せ（nCk 通り）
;;;;   5. do-intervals            : 区間 [l, r] の全列挙（O(N^2) 個）
;;;;      do-rectangles           : 長方形の全列挙（O(H^2 W^2) 個） 例: ABC455 B
;;;;
;;;; 共通ルール
;;;;   - 添字はすべて 0 始まり。
;;;;   - 本体の中で (return) を呼ぶと列挙全体を打ち切る（探索の途中で答えが決まったとき用）。
;;;;     ただし do-intervals / do-rectangles はループが入れ子なので、(return) では
;;;;     いちばん内側しか抜けない。全体を抜けるときは block と return-from を使う。
;;;;   - 列挙用のベクタ（do-tuples / do-permutations / do-combinations の v）は
;;;;     本体の中で書き換えないこと。次の候補を作るのに使っている。
;;;;
;;;; 制約の目安（1 回の判定が O(N) として、2 秒に収まる範囲）
;;;;   N <= 20  → 2^N × N ≒ 2×10^7      bit全探索
;;;;   N <= 10  → N! × N  ≒ 3.6×10^7    順列全探索
;;;;   N <= 12  → 3^N × N ≒ 6×10^6      重複順列（3択）
;;;;   N <= 3000 程度 → N^2             区間の全列挙
;;;;   H, W <= 10〜30 → H^2 W^2 × (判定) 長方形の全列挙

(declaim (optimize (speed 3) (safety 0)))

;;; ------------------------------------------------------------
;;; 1. bit全探索
;;; ------------------------------------------------------------

;; mask を 0, 1, ..., 2^n - 1 と動かす。
;; mask の i ビット目が 1 ⇔ 「i 番目を選ぶ」と読む。
(defmacro do-subsets ((mask n) &body body)
  (let ((gn (gensym "N")))
    `(let ((,gn ,n))
       (declare (type (integer 0 62) ,gn))
       (dotimes (,mask (ash 1 ,gn))
         (declare (type fixnum ,mask))
         ,@body))))

;; mask で 1 になっているビット i（0 <= i < n）だけを回す。
(defmacro do-bits-on ((i mask n) &body body)
  (let ((gm (gensym "MASK")) (gn (gensym "N")))
    `(let ((,gm ,mask) (,gn ,n))
       (declare (type fixnum ,gm ,gn))
       (dotimes (,i ,gn)
         (declare (type fixnum ,i))
         (when (logbitp ,i ,gm)
           ,@body)))))

;;; ------------------------------------------------------------
;;; 2. 重複順列（各位置に 0..k-1 のどれかを入れる、K^N 通り）
;;; ------------------------------------------------------------

;; v は長さ n の fixnum ベクタ。(0 0 ... 0) から (k-1 ... k-1) まで、
;; k 進数のカウンタのように 1 ずつ進める。
(defmacro do-tuples ((v n k) &body body)
  (let ((gn (gensym "N")) (gk (gensym "K")) (gi (gensym "I")))
    `(let* ((,gn ,n) (,gk ,k)
            (,v (make-array ,gn :element-type 'fixnum :initial-element 0)))
       (declare (type fixnum ,gn ,gk)
                (type (simple-array fixnum (*)) ,v))
       (loop
         (progn ,@body)
         ;; 繰り上がり：末尾ではなく先頭（添字 0）から k-1 の桁を 0 に戻していく
         (let ((,gi 0))
           (declare (type fixnum ,gi))
           (loop while (and (< ,gi ,gn) (= (aref ,v ,gi) (1- ,gk)))
                 do (setf (aref ,v ,gi) 0)
                    (incf ,gi))
           (when (= ,gi ,gn) (return))   ; 全桁が k-1 だった → 列挙終了
           (incf (aref ,v ,gi)))))))

;;; ------------------------------------------------------------
;;; 3. 順列
;;; ------------------------------------------------------------

;; v を辞書順で次の順列に書き換えて t を返す。
;; v がすでに辞書順で最後（降順）なら何もせず nil を返す。
;; 同じ値が含まれていても、重複なしで正しく列挙できる。
;;
;; 手順（例: 1 3 5 4 2 → 1 4 2 3 5）
;;   (1) 右から見て、初めて v[i] < v[i+1] となる i を探す（例では v[i]=3）
;;   (2) 右から見て、初めて v[j] > v[i] となる j を探す（例では v[j]=4）
;;   (3) v[i] と v[j] を入れ替える             → 1 4 5 3 2
;;   (4) i+1 以降を反転する（降順 → 昇順）      → 1 4 2 3 5
(defun next-permutation (v)
  (declare (type (simple-array fixnum (*)) v))
  (let* ((n (length v))
         (i (- n 2)))
    (declare (type fixnum n i))
    ;; (1)
    (loop while (and (>= i 0) (>= (aref v i) (aref v (1+ i))))
          do (decf i))
    (when (< i 0)
      (return-from next-permutation nil))
    ;; (2)
    (let ((j (1- n)))
      (declare (type fixnum j))
      (loop while (<= (aref v j) (aref v i))
            do (decf j))
      ;; (3)
      (rotatef (aref v i) (aref v j)))
    ;; (4)
    (loop for l of-type fixnum from (1+ i)
          for r of-type fixnum downfrom (1- n)
          while (< l r)
          do (rotatef (aref v l) (aref v r)))
    t))

;; v = (from, from+1, ..., from+n-1) から始めて、全順列を辞書順に回す。
;; ABC の問題なら :from 1 にすると 1..N の順列になる。
(defmacro do-permutations ((v n &key (from 0)) &body body)
  (let ((gn (gensym "N")) (gf (gensym "FROM")) (gi (gensym "I")))
    `(let* ((,gn ,n) (,gf ,from)
            (,v (make-array ,gn :element-type 'fixnum)))
       (declare (type fixnum ,gn ,gf)
                (type (simple-array fixnum (*)) ,v))
       (dotimes (,gi ,gn)
         (setf (aref ,v ,gi) (+ ,gf ,gi)))
       (loop
         (progn ,@body)
         (unless (next-permutation ,v) (return))))))

;;; ------------------------------------------------------------
;;; 4. 組合せ（0..n-1 から k 個を選ぶ、nCk 通り）
;;; ------------------------------------------------------------

;; v は長さ k の昇順の添字列。(0 1 ... k-1) から (n-k ... n-1) まで辞書順に回す。
;; k = 0 のときは「何も選ばない」1 通りだけ本体を実行する。
(defmacro do-combinations ((v n k) &body body)
  (let ((gn (gensym "N")) (gk (gensym "K")) (gi (gensym "I")) (gj (gensym "J")))
    `(let* ((,gn ,n) (,gk ,k)
            (,v (make-array ,gk :element-type 'fixnum)))
       (declare (type fixnum ,gn ,gk)
                (type (simple-array fixnum (*)) ,v))
       (when (<= ,gk ,gn)
         (dotimes (,gi ,gk)
           (setf (aref ,v ,gi) ,gi))
         (loop
           (progn ,@body)
           ;; 右から見て、まだ増やせる位置 i（v[i] < n-k+i）を探す
           (let ((,gi (1- ,gk)))
             (declare (type fixnum ,gi))
             (loop while (and (>= ,gi 0)
                              (= (aref ,v ,gi) (+ (- ,gn ,gk) ,gi)))
                   do (decf ,gi))
             (when (< ,gi 0) (return))
             (incf (aref ,v ,gi))
             ;; i より右は「直前 + 1」で詰め直す
             (loop for ,gj of-type fixnum from (1+ ,gi) below ,gk
                   do (setf (aref ,v ,gj) (1+ (aref ,v (1- ,gj)))))))))))

;;; ------------------------------------------------------------
;;; 5. 区間・長方形の全列挙
;;; ------------------------------------------------------------

;; 0 <= l <= r < n を満たす全ての区間 [l, r]（両端を含む）。
(defmacro do-intervals ((l r n) &body body)
  (let ((gn (gensym "N")))
    `(let ((,gn ,n))
       (declare (type fixnum ,gn))
       (loop for ,l of-type fixnum from 0 below ,gn
             do (loop for ,r of-type fixnum from ,l below ,gn
                      do (progn ,@body))))))

;; 行 [h1, h2]・列 [w1, w2]（両端を含む）の長方形を全て回す。
;; 0 <= h1 <= h2 < h, 0 <= w1 <= w2 < w。
(defmacro do-rectangles ((h1 h2 w1 w2 h w) &body body)
  (let ((gh (gensym "H")) (gw (gensym "W")))
    `(let ((,gh ,h) (,gw ,w))
       (declare (type fixnum ,gh ,gw))
       (do-intervals (,h1 ,h2 ,gh)
         (do-intervals (,w1 ,w2 ,gw)
           ,@body)))))
