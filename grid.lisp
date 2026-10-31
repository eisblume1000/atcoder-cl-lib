;;;; grid.lisp — グリッド(H 行 W 列の文字)の読み込み・出力・隣接マスの走査
;;;; https://github.com/eisblume1000/atcoder-cl-lib
;;;;
;;;; 前提: fastio.lisp の後ろに置く(read-token-bytes, fast-write-byte を使う)。
;;;;
;;;; グリッドは (simple-array (unsigned-byte 8) (* *)) で持つ。各マスは文字コード。
;;;;   文字との比較は (= (aref g i j) #.(char-code #\#)) のように書く。
;;;;   #.(char-code #\#) は読み込み時に 35 に置き換わるので、実行時の変換はない。
;;;;
;;;; ════════════════════════════════════════════════════════════════
;;;; (read-grid h w &key (pad 0) (pad-char #\#) digits) → grid
;;;; ════════════════════════════════════════════════════════════════
;;;;   H 行 W 列のグリッドを読む。入力は 1 行に W 文字(空白なし)が H 行並ぶ形式。
;;;;     pad      : 周りに何マスの枠を付けるか。0 なら枠なし。
;;;;     pad-char : 枠のマスに入れる文字(既定は #\#、つまり壁)。
;;;;     digits   : t なら各マスを数字(0..9)として読む(文字コード - 48)。
;;;;
;;;;   配列の大きさと添字:
;;;;     pad = 0 … (h, w)。マス (i, j) は (aref g i j)、0 <= i < h, 0 <= j < w
;;;;     pad = 1 … (h+2, w+2)。マス (i, j) は 1 <= i <= h, 1 <= j <= w(自然に 1-indexed になる)
;;;;
;;;;   枠を付ける理由:
;;;;     枠を壁にしておくと、隣のマスへ進むときに「グリッドの外に出たか」を確かめなくてよい。
;;;;     外側はすべて壁なので、壁かどうかの判定だけで済む。BFS・DFS でよく使う。
;;;;
;;;;   例:
;;;;     (let* ((h (read-fixnum)) (w (read-fixnum))
;;;;            (g (read-grid h w :pad 1)))          ; 周りを # で囲む
;;;;       (= (aref g 1 1) #.(char-code #\.)))      ; 左上のマスが '.' か
;;;;
;;;; ════════════════════════════════════════════════════════════════
;;;; (write-grid g &key (pad 0) digits)
;;;; ════════════════════════════════════════════════════════════════
;;;;   グリッドを 1 行ずつ出力する(枠の部分は出さない)。最後に (flush-out) を忘れないこと。
;;;;     pad    : read-grid で付けた枠の幅と同じ値を渡す。
;;;;     digits : t なら各マスを数字として出力する(+ 48 して書く)。
;;;;
;;;; ════════════════════════════════════════════════════════════════
;;;; (do-neighbors ((ni nj) (i j) &key bounds diagonal) body...)
;;;; ════════════════════════════════════════════════════════════════
;;;;   マス (i, j) の隣のマス (ni, nj) それぞれについて body を実行する。
;;;;     bounds   : (h w) を書くと、0 <= ni < h, 0 <= nj < w のマスだけに絞る。
;;;;                枠付きのグリッドなら省略してよい(外に出る心配がない)。
;;;;     diagonal : t なら斜めも含めた 8 方向。既定は上下左右の 4 方向。
;;;;   順番は 上・下・左・右(diagonal なら続けて 左上・右上・左下・右下)。
;;;;   body は方向の数だけ展開される(ループより速い)ので、長い処理は関数にして呼ぶとよい。
;;;;
;;;;   例: 枠付きグリッドで BFS(距離は -1 で未訪問)
;;;;     (do-neighbors ((ni nj) (i j))
;;;;       (when (and (/= (aref g ni nj) #.(char-code #\#))
;;;;                  (= (aref dist ni nj) -1))
;;;;         (setf (aref dist ni nj) (1+ (aref dist i j)))
;;;;         ... キューに (ni, nj) を入れる ...))
;;;;
;;;;   例: 枠なしグリッドで、範囲内の隣だけ数える
;;;;     (do-neighbors ((ni nj) (i j) :bounds (h w))
;;;;       (when (= (aref g ni nj) #.(char-code #\#)) (incf cnt)))
;;;;
;;;; 前提・制限
;;;;   - 各行は空白を含まず、ちょうど W 文字であること(検査しない)。
;;;;   - safety 0 前提で範囲検査はしない。

(declaim (optimize (speed 3) (safety 0) (debug 0)))

(deftype grid () '(simple-array (unsigned-byte 8) (* *)))

;;; ───────── 読み込み ─────────

(defun read-grid (h w &key (pad 0) (pad-char #\#) digits)
  (declare (type fixnum h w) (type (integer 0 1024) pad) (type character pad-char))
  (let ((g (make-array (list (+ h (* 2 pad)) (+ w (* 2 pad)))
                       :element-type '(unsigned-byte 8)
                       :initial-element (if (plusp pad) (char-code pad-char) 0))))
    (declare (type grid g))
    (dotimes (i h)
      (let ((row (read-token-bytes)))
        (declare (type u8vec row))
        (if digits
            (dotimes (j w)
              (setf (aref g (+ i pad) (+ j pad)) (- (aref row j) 48)))
            (dotimes (j w)
              (setf (aref g (+ i pad) (+ j pad)) (aref row j))))))
    g))

;;; ───────── 出力 ─────────

(defun write-grid (g &key (pad 0) digits)
  (declare (type grid g) (type (integer 0 1024) pad))
  (let ((h (- (array-dimension g 0) (* 2 pad)))
        (w (- (array-dimension g 1) (* 2 pad))))
    (declare (type fixnum h w))
    (dotimes (i h)
      (if digits
          (dotimes (j w)
            (fast-write-byte (+ 48 (aref g (+ i pad) (+ j pad)))))
          (dotimes (j w)
            (fast-write-byte (aref g (+ i pad) (+ j pad)))))
      (fast-write-byte 10))
    nil))

;;; ───────── 隣接マスの走査 ─────────

(defmacro do-neighbors (((ni nj) (i j) &key bounds diagonal) &body body)
  (declare (optimize (speed 1)))           ; マクロ本体(展開処理)の note を抑える
  (let* ((dirs (append '((-1 0) (1 0) (0 -1) (0 1))
                       (when diagonal '((-1 -1) (-1 1) (1 -1) (1 1)))))
         (ci (gensym "I")) (cj (gensym "J"))
         (h (gensym "H")) (w (gensym "W")))
    `(let ((,ci ,i) (,cj ,j)
           ,@(when bounds `((,h ,(first bounds)) (,w ,(second bounds)))))
       (declare (type fixnum ,ci ,cj ,@(when bounds (list h w)))
                (ignorable ,ci ,cj))
       ,@(loop for (di dj) in dirs
               collect
               `(let ((,ni (+ ,ci ,di)) (,nj (+ ,cj ,dj)))
                  (declare (type fixnum ,ni ,nj) (ignorable ,ni ,nj))
                  ,(if bounds
                       `(when (and ,@(unless (zerop di)
                                       (if (minusp di) `((>= ,ni 0)) `((< ,ni ,h))))
                                   ,@(unless (zerop dj)
                                       (if (minusp dj) `((>= ,nj 0)) `((< ,nj ,w)))))
                          ,@body)
                       `(progn ,@body)))))))
