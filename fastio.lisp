;;;; fastio.lisp — AtCoder向け SBCL 高速I/Oユーティリティ(文字列対応版)
;;;; https://github.com/eisblume1000/atcoder-cl-lib/edit/main/fastio.lisp
;;;; 生成AIで作成。
;;;;
;;;; 入力
;;;;   (read-fixnum)           空白区切りの整数(負数可、fixnumの範囲)
;;;;   (read-nonspace-byte)    空白以外の1バイト。EOFで -1  (グリッドの '#' '.' など)
;;;;   (read-digit)            空白以外の1文字を数字(0..9)として返す
;;;;   (read-string)           空白区切りの文字列 → (simple-array character (*))
;;;;   (read-token-bytes)      同じトークンを (simple-array (unsigned-byte 8) (*)) で返す
;;;;                           ※文字を (aref s i) と文字コードで比較するだけならこちらが速くて省メモリ
;;;;   (read-fixnum-array n)   / (read-fixnum-array-1 n) (1-indexed、[0]=0)
;;;;   (fast-read-byte)        互換用。生の1バイト(空白含む)。EOFで -1。ホットループ向きではない
;;;; 出力
;;;;   (write-fixnum n) (fast-write-byte b) (fast-write-char c)
;;;;   (fast-write-string s) (fast-write-bytes v)   最後に必ず (flush-out)
;;;;
;;;; 前提・制限
;;;;   - 数値トークンは +in-slack+ (32) バイト未満。数字判定は (>= c 48) のみ。
;;;;   - 文字列の長さに上限なし(入力バッファをまたぐ長い文字列も可)。
;;;;   - 入出力はASCII前提。出力は1文字を下位8bitで書く(非ASCIIは文字化けする)。
(declaim (optimize (speed 3) (safety 0) (debug 0)))

(defconstant +in-size+  (ash 1 16))
(defconstant +in-slack+ 32)
(defconstant +out-size+ (ash 1 16))

(deftype u8vec () '(simple-array (unsigned-byte 8) (*)))
(deftype cstring () '(simple-array character (*)))

(sb-ext:defglobal *in-buf*  (make-array (+ +in-size+ 1) :element-type '(unsigned-byte 8) :initial-element 0))
(sb-ext:defglobal *in-pos* 0)
(sb-ext:defglobal *in-end* 0)
;; write-fixnum が1数値ぶん(<=21B)を無条件で書けるよう、実サイズに余白を持たせる
(sb-ext:defglobal *out-buf* (make-array (+ +out-size+ 32) :element-type '(unsigned-byte 8) :initial-element 0))
(sb-ext:defglobal *out-pos* 0)
(declaim (type u8vec *in-buf* *out-buf*)
         (type fixnum *in-pos* *in-end* *out-pos*))

;;; ───────── 入力: 補充(遅いパス) ─────────

;; 未読バイトを先頭へ詰め直し、+in-slack+ バイト以上たまる(またはEOF)まで読む。
;; 64KB に 1 回しか呼ばれない遅いパスなので、システムコール周りの型変換の note は抑える。
(declaim (notinline %refill))
(defun %refill ()
  (declare (sb-ext:muffle-conditions sb-ext:compiler-note))
  (let* ((buf *in-buf*) (pos *in-pos*) (end *in-end*) (rem (- end pos)))
    (declare (type fixnum pos end rem))
    (dotimes (i rem) (setf (aref buf i) (aref buf (+ pos i))))
    (setf end rem)
    (sb-sys:with-pinned-objects (buf)
      (loop while (< end +in-slack+)
            do (let ((r (sb-unix:unix-read 0 (sb-sys:sap+ (sb-sys:vector-sap buf) end)
                                           (- +in-size+ end))))
                 (if (and r (> (the fixnum r) 0))
                     (incf end (the fixnum r))
                     (return)))))
    (setf (aref buf end) 0)           ; 番兵
    (setf *in-pos* 0 *in-end* end)
    nil))

;; 空白(<=32)を読み飛ばす。EOFなら pos >= *in-end* で終わる。
(defmacro %skip-ws (pos)
  `(loop
     (when (>= ,pos *in-end*)
       (setf *in-pos* ,pos) (%refill) (setf ,pos *in-pos*)
       (when (>= ,pos *in-end*) (return)))
     (when (> (aref *in-buf* ,pos) 32) (return))
     (incf ,pos)))

;; 空白を飛ばしたうえで、トークン先頭から +in-slack+ バイト以上を保証する。
;; 以後のトークン内では範囲チェック不要(終端は番兵0)。
(defmacro %to-token (pos)
  `(progn
     (%skip-ws ,pos)
     (when (< (- *in-end* ,pos) +in-slack+)
       (setf *in-pos* ,pos) (%refill) (setf ,pos *in-pos*))))

;;; ───────── 入力: 数値・1バイト ─────────

(declaim (inline read-fixnum read-nonspace-byte read-digit fast-read-byte))

(defun read-fixnum ()
  (let ((pos *in-pos*) (buf *in-buf*) (n 0) (neg nil))
    (declare (type fixnum pos n) (type u8vec buf))
    (%to-token pos)
    (let ((c (aref buf pos)))
      (declare (type fixnum c))
      (when (= c 45) (setf neg t) (incf pos) (setf c (aref buf pos)))
      (loop while (>= c 48)
            do (setf n (the fixnum (+ (the fixnum (* n 10)) (the fixnum (- c 48)))))
               (incf pos)
               (setf c (aref buf pos))))
    (setf *in-pos* pos)
    (if neg (the fixnum (- n)) n)))

(defun read-nonspace-byte ()
  (let ((pos *in-pos*))
    (declare (type fixnum pos))
    (%to-token pos)
    (if (>= pos *in-end*)
        (progn (setf *in-pos* pos) -1)
        (prog1 (the fixnum (aref *in-buf* pos))
          (setf *in-pos* (1+ pos))))))

(defun read-digit ()
  (the fixnum (- (the fixnum (read-nonspace-byte)) 48)))

(defun fast-read-byte ()
  (when (>= *in-pos* *in-end*) (%refill))
  (if (>= *in-pos* *in-end*)
      -1
      (prog1 (the fixnum (aref *in-buf* *in-pos*))
        (incf *in-pos*))))

;;; ───────── 入力: 文字列 ─────────

(declaim (ftype (function () u8vec) read-token-bytes)
         (ftype (function () cstring) read-string)
         (ftype (function (fixnum) (simple-array fixnum (*))) read-fixnum-array read-fixnum-array-1))

;; 空白区切りトークンをバイト列で返す。バッファ内で終わるなら1回のコピーだけ。
;; バッファをまたぐ長いトークンは、区間ごとに作業配列へ貯めて最後に切り出す。
(defun read-token-bytes ()
  (let ((pos *in-pos*) (buf *in-buf*))
    (declare (type fixnum pos) (type u8vec buf))
    (%skip-ws pos)
    (let ((start pos) (end *in-end*) (acc nil) (n 0))
      (declare (type fixnum start end n) (type (or null u8vec) acc))
      (loop
        (loop while (and (< pos end) (> (aref buf pos) 32)) do (incf pos))
        (cond
          ((< pos end)                  ; バッファ内で終端が見つかった
           (setf *in-pos* pos)
           (return
             (if (null acc)
                 (subseq buf start pos)
                 (let ((len (- pos start)))
                   (declare (type fixnum len))
                   (when (> (the fixnum (+ n len)) (length acc))
                     (let ((new (make-array (the fixnum (* 2 (the fixnum (+ n len))))
                                            :element-type '(unsigned-byte 8))))
                       (replace new acc :end2 n) (setf acc new)))
                   (replace acc buf :start1 n :start2 start :end2 pos)
                   (incf n len)
                   (subseq acc 0 n)))))
          (t                            ; バッファ末尾まで到達 → 作業配列に退避して補充
           (let ((len (- pos start)))
             (declare (type fixnum len))
             (when (or (null acc) (> (the fixnum (+ n len)) (length acc)))
               (let ((new (make-array (max 4096 (the fixnum (* 2 (the fixnum (+ n len)))))
                                      :element-type '(unsigned-byte 8))))
                 (when acc (replace new acc :end2 n))
                 (setf acc new)))
             (replace acc buf :start1 n :start2 start :end2 pos)
             (incf n len))
           (setf *in-pos* pos)
           (%refill)
           (setf start 0 pos 0 end *in-end*)
           (when (= end 0)              ; EOF(ここに来るときは acc は必ず確保済み)
             (return (subseq acc 0 n)))))))))

(defun read-string ()
  (let ((pos *in-pos*) (buf *in-buf*))
    (declare (type fixnum pos) (type u8vec buf))
    (%skip-ws pos)
    (let ((start pos) (end *in-end*))
      (declare (type fixnum start end))
      (loop while (and (< pos end) (> (aref buf pos) 32)) do (incf pos))
      (if (or (< pos end) (= start end))
          ;; 典型パス: バッファ内で終わる → 1回で直接 string へ
          (let* ((len (- pos start))
                 (s (make-string len)))
            (declare (type fixnum len) (type cstring s))
            (dotimes (i len) (setf (schar s i) (code-char (aref buf (+ start i)))))
            (setf *in-pos* pos)
            s)
          ;; 長い文字列: 先頭から読み直してバイト列経由で変換
          (progn
            (setf *in-pos* start)
            (let* ((b (read-token-bytes)) (len (length b)) (s (make-string len)))
              (declare (type u8vec b) (type fixnum len) (type cstring s))
              (dotimes (i len) (setf (schar s i) (code-char (aref b i))))
              s))))))

(defun read-fixnum-array (size)
  (declare (type fixnum size))
  (let ((arr (make-array size :element-type 'fixnum)))
    (dotimes (i size arr)
      (setf (aref arr i) (read-fixnum)))))

(defun read-fixnum-array-1 (size)
  (declare (type fixnum size))
  (let ((arr (make-array (1+ size) :element-type 'fixnum :initial-element 0)))
    (loop for i of-type fixnum from 1 to size
          do (setf (aref arr i) (read-fixnum)))
    arr))

;;; ───────── 出力 ─────────

;; flush-out は 64KB に 1 回しか呼ばれない遅いパスなので inline にしない。
;; (inline にすると、fast-write-byte などを呼ぶ場所すべてにシステムコールのコードが
;;  展開され、コードが膨らむうえ、呼び出し側にまで note が出る)
(declaim (notinline flush-out))
(defun flush-out ()
  (declare (sb-ext:muffle-conditions sb-ext:compiler-note))
  (let ((buf *out-buf*) (n *out-pos*) (off 0))
    (declare (type fixnum n off))
    (sb-sys:with-pinned-objects (buf)
      (loop while (< off n)
            do (let ((r (sb-unix:unix-write 1 buf off (the fixnum (- n off)))))
                 (if (and r (> (the fixnum r) 0))
                     (incf off (the fixnum r))
                     (return)))))
    (setf *out-pos* 0)
    nil))

(declaim (inline fast-write-byte fast-write-char write-fixnum))

(defun fast-write-byte (b)
  (declare (type (unsigned-byte 8) b))
  (when (>= *out-pos* +out-size+) (flush-out))
  (setf (aref *out-buf* *out-pos*) b)
  (incf *out-pos*))

(defun fast-write-char (c)
  (declare (type character c))
  (fast-write-byte (logand #xff (char-code c))))

(defun write-fixnum (n)
  (declare (type fixnum n))
  (when (>= *out-pos* +out-size+) (flush-out))   ; 以後32B以上の余白がある
  (let ((pos *out-pos*) (buf *out-buf*) (v 0) (len 1) (t10 10))
    (declare (type fixnum pos len) (type u8vec buf)
             (type (unsigned-byte 64) v t10))
    (if (< n 0)
        (progn (setf (aref buf pos) 45) (incf pos)
               (setf v (the (unsigned-byte 64) (- n))))   ; most-negative-fixnum でも安全
        (setf v n))
    (loop while (>= v t10) do (incf len) (setf t10 (* t10 10)))
    (let ((p (+ pos len)))
      (declare (type fixnum p))
      (setf *out-pos* p)
      (loop repeat len
            do (decf p)
               (multiple-value-bind (q r) (truncate v 10)
                 (declare (type (unsigned-byte 64) q) (type (integer 0 9) r))
                 (setf (aref buf p) (+ 48 r))
                 (setf v q))))))

;; 1バイト列(コード列)を範囲 [start,end) だけ書く共通部
(defmacro %write-run (len code-form)
  `(let ((i 0))
     (declare (type fixnum i))
     (loop while (< i ,len)
           do (when (>= *out-pos* +out-size+) (flush-out))
              (let* ((pos *out-pos*) (buf *out-buf*)
                     (m (min (- +out-size+ pos) (- ,len i))))
                (declare (type fixnum pos m) (type u8vec buf))
                (dotimes (k m)
                  (setf (aref buf (+ pos k)) (logand #xff ,code-form)))
                (incf i m)
                (setf *out-pos* (+ pos m))))))

(defun fast-write-string (s)
  (declare (type string s))
  (typecase s
    (cstring
     (let ((len (length s)))
       (declare (type fixnum len))
       (%write-run len (char-code (schar s (+ i k))))))
    (simple-base-string
     (let ((len (length s)))
       (declare (type fixnum len))
       (%write-run len (char-code (schar s (+ i k))))))
    (t (fast-write-string (coerce s 'cstring)))))

(defun fast-write-bytes (v)
  (declare (type u8vec v))
  (let ((len (length v)))
    (declare (type fixnum len))
    (%write-run len (aref v (+ i k)))))

(deftype u8  () '(unsigned-byte 8))
(deftype u16 () '(unsigned-byte 16))
(deftype u32 () '(unsigned-byte 32))
(deftype u64 () '(unsigned-byte 64))
(deftype i8  () '(signed-byte 8))
(deftype i16 () '(signed-byte 16))
(deftype i32 () '(signed-byte 32))
(deftype i64 () '(signed-byte 64))
(deftype arr1 (&optional (type '*)) `(simple-array ,type (*)))
(deftype arr2 (&optional (type '*)) `(simple-array ,type (* *)))
