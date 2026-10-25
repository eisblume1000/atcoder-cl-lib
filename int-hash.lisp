;;;; int-hash.lisp — AtCoder向け SBCL 整数キー専用ハッシュテーブル
;;;; https://github.com/eisblume1000/atcoder-cl-lib
;;;;
;;;; fastio.lisp の後ろに置いて使う(read-word-key が fastio の入力バッファを読むため)。
;;;; ハッシュテーブル本体(ihash-*)は fastio に依存しない。
;;;;
;;;; 概要
;;;;   キーも値も fixnum。オープンアドレス法(線形探索)+ 乗算ハッシュ。
;;;;   標準の make-hash-table より速く、文字列は read-word-key で整数に符号化して使う。
;;;;
;;;; テーブル
;;;;   (make-ihash &optional (bits 16))  容量 2^bits で作る。満杯に近づくと自動で倍に拡張
;;;;   (ihash-count h)                   登録されているキーの数
;;;;   (ihash-clear h)                   全消去(容量はそのまま)
;;;;
;;;; 基本操作
;;;;   (ihash-get h key &optional (default -1))   値。無ければ default
;;;;   (ihash-has h key)                          キーがあるか
;;;;   (ihash-put h key val)                      登録・上書き。val を返す
;;;;   (ihash-add h key d)                        値に d を足す(無ければ 0 から)。新しい値を返す
;;;;   (ihash-get-or-put h key val)               あればその値、無ければ val を登録。
;;;;                                              返り値 (values 値 既にあったか)
;;;;   (ihash-map h fn)                           全要素に (funcall fn key val)。順序は不定
;;;;
;;;; 入力(fastio 依存)
;;;;   (read-lower-key)                 英小文字の単語 → 正の fixnum(12 文字まで)
;;;;   (read-word-key offset bits)      一般形。文字コード - offset を bits ビットずつ詰める
;;;;                                    offset は「使う最小の文字コード - 1」にすること
;;;;                                    例: 英大文字 (read-word-key 64 5)
;;;;                                        英数字   (read-word-key 47 7)  ; '0'..'z' 8 文字まで
;;;;
;;;; 前提・制限
;;;;   - キーは most-negative-fixnum 以外の fixnum(空きの印に使うため)。負や 0 も可。
;;;;   - 削除は無い(必要なら ihash-clear で丸ごと)。
;;;;   - read-*-key は単語長 × bits <= 62 であること。超えると符号化が壊れる(検査しない)。
;;;;     単語長は fastio の +in-slack+ (32) 未満であること。
;;;;   - safety 0 前提で範囲検査はしない。
;;;;   - 初期容量は「最大要素数 × 2」以上の 2 のべきにしておくと拡張が起きず速い。
;;;;     (例: 2×10^5 要素なら bits = 19。足りなくても自動拡張されるので結果は正しい)
;;;;
;;;; 使用例(ABC481 C - Bank Accounts)
;;;;   (defun main ()
;;;;     (let ((q (read-fixnum)) (h (make-ihash 19)) (next-id 1))
;;;;       (declare (type fixnum q next-id))
;;;;       (loop repeat q do
;;;;         (multiple-value-bind (id existed)
;;;;             (ihash-get-or-put h (read-lower-key) next-id)
;;;;           (unless existed (incf next-id))
;;;;           (write-fixnum id) (fast-write-byte 10))))
;;;;     (flush-out))

(declaim (optimize (speed 3) (safety 0) (debug 0)))

(defconstant +ihash-empty+ most-negative-fixnum)

(defstruct (ihash (:constructor %make-ihash (bits keys vals)))
  (bits  0 :type (integer 1 60))
  (count 0 :type (unsigned-byte 60))
  (keys  nil :type (simple-array fixnum (*)))
  (vals  nil :type (simple-array fixnum (*))))

(defun make-ihash (&optional (bits 16))
  (declare (type (integer 1 60) bits))
  (%make-ihash bits
               (make-array (ash 1 bits) :element-type 'fixnum
                                        :initial-element +ihash-empty+)
               (make-array (ash 1 bits) :element-type 'fixnum
                                        :initial-element 0)))

;;; ───────── 内部 ─────────

;; key がある位置、無ければ key を入れるべき空き位置
(declaim (inline %ihash-slot))
(defun %ihash-slot (keys bits key)
  (declare (type (simple-array fixnum (*)) keys)
           (type (integer 1 60) bits)
           (type fixnum key))
  (let ((mask (1- (ash 1 bits)))
        (i (ash (ldb (byte 64 0) (* (ldb (byte 64 0) key) #x9E3779B97F4A7C15))
                (- bits 64))))
    (declare (type fixnum mask i))
    (loop
      (let ((k (aref keys i)))
        (when (or (= k key) (= k +ihash-empty+))
          (return i))
        (setf i (logand (1+ i) mask))))))

;; 容量を倍にして全要素を入れ直す
(declaim (notinline %ihash-grow))
(defun %ihash-grow (h)
  (declare (type ihash h))
  (let* ((old-keys (ihash-keys h))
         (old-vals (ihash-vals h))
         (bits (1+ (ihash-bits h)))
         (keys (make-array (ash 1 bits) :element-type 'fixnum
                                        :initial-element +ihash-empty+))
         (vals (make-array (ash 1 bits) :element-type 'fixnum
                                        :initial-element 0)))
    (dotimes (j (length old-keys))
      (let ((k (aref old-keys j)))
        (unless (= k +ihash-empty+)
          (let ((i (%ihash-slot keys bits k)))
            (setf (aref keys i) k
                  (aref vals i) (aref old-vals j))))))
    (setf (ihash-bits h) bits
          (ihash-keys h) keys
          (ihash-vals h) vals)
    h))

;; 新規登録の直前に呼ぶ。埋まり具合を 1/2 以下に保つ
(declaim (inline %ihash-reserve))
(defun %ihash-reserve (h)
  (declare (type ihash h))
  (when (>= (the fixnum (* 2 (1+ (ihash-count h)))) (ash 1 (ihash-bits h)))
    (%ihash-grow h)))

;;; ───────── 公開 API ─────────

(declaim (inline ihash-get ihash-has ihash-put ihash-add ihash-get-or-put))

(defun ihash-get (h key &optional (default -1))
  (declare (type ihash h) (type fixnum key default))
  (let* ((keys (ihash-keys h))
         (i (%ihash-slot keys (ihash-bits h) key)))
    (declare (type fixnum i))
    (if (= (aref keys i) key)
        (aref (ihash-vals h) i)
        default)))

(defun ihash-has (h key)
  (declare (type ihash h) (type fixnum key))
  (let* ((keys (ihash-keys h))
         (i (%ihash-slot keys (ihash-bits h) key)))
    (declare (type fixnum i))
    (= (aref keys i) key)))

(defun ihash-put (h key val)
  (declare (type ihash h) (type fixnum key val))
  (let ((i (%ihash-slot (ihash-keys h) (ihash-bits h) key)))
    (declare (type fixnum i))
    (when (= (aref (ihash-keys h) i) +ihash-empty+)
      (%ihash-reserve h)
      ;; 拡張された場合は位置が変わるので探し直す
      (setf i (%ihash-slot (ihash-keys h) (ihash-bits h) key))
      (setf (aref (ihash-keys h) i) key)
      (incf (ihash-count h)))
    (setf (aref (ihash-vals h) i) val)))

(defun ihash-add (h key d)
  (declare (type ihash h) (type fixnum key d))
  (let ((i (%ihash-slot (ihash-keys h) (ihash-bits h) key)))
    (declare (type fixnum i))
    (when (= (aref (ihash-keys h) i) +ihash-empty+)
      (%ihash-reserve h)
      (setf i (%ihash-slot (ihash-keys h) (ihash-bits h) key))
      (setf (aref (ihash-keys h) i) key
            (aref (ihash-vals h) i) 0)
      (incf (ihash-count h)))
    (setf (aref (ihash-vals h) i)
          (the fixnum (+ (aref (ihash-vals h) i) d)))))

(defun ihash-get-or-put (h key val)
  (declare (type ihash h) (type fixnum key val))
  (let ((i (%ihash-slot (ihash-keys h) (ihash-bits h) key)))
    (declare (type fixnum i))
    (if (= (aref (ihash-keys h) i) key)
        (values (aref (ihash-vals h) i) t)
        (progn
          (%ihash-reserve h)
          (setf i (%ihash-slot (ihash-keys h) (ihash-bits h) key))
          (setf (aref (ihash-keys h) i) key
                (aref (ihash-vals h) i) val)
          (incf (ihash-count h))
          (values val nil)))))

(defun ihash-clear (h)
  (declare (type ihash h))
  (fill (ihash-keys h) +ihash-empty+)
  (setf (ihash-count h) 0)
  h)

(defun ihash-map (h fn)
  (declare (type ihash h) (type function fn))
  (let ((keys (ihash-keys h)) (vals (ihash-vals h)))
    (dotimes (i (length keys))
      (let ((k (aref keys i)))
        (unless (= k +ihash-empty+)
          (funcall fn k (aref vals i))))))
  nil)

;;; ───────── 入力: 単語を整数キーとして読む(fastio 依存) ─────────

(declaim (inline read-word-key read-lower-key))

(defun read-word-key (offset bits)
  (declare (type fixnum offset) (type (integer 1 62) bits))
  (let ((pos *in-pos*) (buf *in-buf*) (k 0))
    (declare (type fixnum pos k) (type u8vec buf))
    (%to-token pos)
    (loop for c of-type fixnum = (aref buf pos)
          while (> c 32)
          do (setf k (logior (the fixnum (ash k bits)) (- c offset)))
             (incf pos))
    (setf *in-pos* pos)
    k))

(defun read-lower-key ()
  (read-word-key 96 5))
