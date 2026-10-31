;;;; mod.lisp — mod 計算(四則演算・べき乗・逆元・二項係数・等比数列の和)
;;;; https://github.com/eisblume1000/atcoder-cl-lib
;;;;
;;;; 前提: fastio.lisp の後ろに置く。
;;;;
;;;; ════════════════════════════════════════════════════════════════
;;;; mod の値
;;;; ════════════════════════════════════════════════════════════════
;;;;   (defconstant +mod+ 998244353)   ← 問題に合わせてこの 1 行を書き換える
;;;;   最近の AtCoder(ABC など)は 998244353 がほとんど。10^9+7 の問題なら 1000000007 にする。
;;;;
;;;;   下の関数はすべて最後の引数 m を省略でき、省略すると +mod+ を使う。
;;;;   別の mod を使いたいときだけ m を渡す。
;;;;   mod が定数だと、SBCL は (mod x +mod+) を割り算命令ではなく掛け算とシフトで計算する
;;;;   (手元の計測では、変数で渡す場合と比べて 0〜2 割程度速い)。
;;;;
;;;; ════════════════════════════════════════════════════════════════
;;;; 基本演算(結果は必ず 0 .. m-1。負の数を渡してもよい)
;;;; ════════════════════════════════════════════════════════════════
;;;;   (mod+ a b &optional m)      a + b
;;;;   (mod- a b &optional m)      a - b
;;;;   (mod* a b &optional m)      a * b
;;;;   (mod-pow a b &optional m)   a^b(b >= 0。繰り返し二乗法、O(log b))
;;;;   (mod-inv a &optional m)     a の逆元(a * x ≡ 1 となる x)
;;;;   (mod-div a b &optional m)   a / b
;;;;     mod-inv と mod-div はフェルマーの小定理を使うので、m が素数で b が m の倍数でないこと。
;;;;
;;;;   例: DP の遷移
;;;;     (setf (aref dp i) (mod+ (aref dp (- i 1)) (aref dp (- i 2))))
;;;;   例: 1/2 mod p
;;;;     (mod-inv 2)                  ; → 499122177(998244353 のとき)
;;;;
;;;; ════════════════════════════════════════════════════════════════
;;;; 二項係数(表を使う版): n が 10^7 程度まで、何度も計算するとき
;;;; ════════════════════════════════════════════════════════════════
;;;;   (init-fact max-n)   0! .. max-n! とその逆元の表を作る。O(max-n)。最初に 1 回だけ呼ぶ
;;;;   (fact n)            n!
;;;;   (inv-fact n)        1/n!
;;;;   (ncr n r)           nCr  … n 個から r 個選ぶ
;;;;   (npr n r)           nPr  … n 個から r 個選んで並べる
;;;;   (nhr n r)           nHr  … n 種類から重複を許して r 個選ぶ(= (n+r-1)Cr)
;;;;     r < 0, r > n などありえない組では 0 を返す。O(1)。
;;;;     表は +mod+ で作る(m は渡せない)。
;;;;     max-n は「使う n の最大値」。nhr では n+r-1 まで必要。範囲は検査しないので注意。
;;;;
;;;;   例: パスカルの三角形の 1 行ぶん
;;;;     (init-fact 200000)
;;;;     (loop for r from 0 to n collect (ncr n r))
;;;;
;;;; ════════════════════════════════════════════════════════════════
;;;; 二項係数(n が大きい版): n が 10^18 などで表を作れないとき
;;;; ════════════════════════════════════════════════════════════════
;;;;   (ncr-large n r &optional m)
;;;;     n(n-1)…(n-r+1) / r! を直接計算する。O(min(r, n-r))。表は不要。
;;;;     n はどんなに大きくてもよい。min(r, n-r) < m かつ m が素数であること。
;;;;     1 回だけ nCr が欲しいときにも使える。
;;;;
;;;;   例: (ncr-large 1000000000000000000 3)
;;;;
;;;; ════════════════════════════════════════════════════════════════
;;;; 等比数列の和
;;;; ════════════════════════════════════════════════════════════════
;;;;   (mod-geometric-sum a1 r n &optional m)
;;;;     a1 + a1*r + a1*r^2 + … + a1*r^(n-1)(n 項の和)。O(log n)。
;;;;     r ≡ 1 (mod m) のときは a1*n。それ以外は a1(r^n - 1)/(r - 1) で、m が素数であること。
;;;;
;;;;   例: 1 + 2 + 4 + … + 2^(n-1)
;;;;     (mod-geometric-sum 1 2 n)
;;;;
;;;; 前提・制限
;;;;   - m は 2 以上 2^31 未満(2 つの値の積が fixnum に収まる条件)。998244353, 10^9+7 は OK。
;;;;   - 引数は fixnum。mod+ / mod- は |a|, |b| < 2^61 であること(和が fixnum に収まるため)。

(declaim (optimize (speed 3) (safety 0) (debug 0)))

(defconstant +mod+ 998244353)

;; m の型。2 つの値の積 < m^2 < 2^62 が fixnum に収まる範囲
(deftype %modulus () '(integer 2 (2147483648)))

;;; ───────── 基本演算 ─────────

(declaim (inline mod+ mod- mod* mod-pow mod-inv mod-div))

(defun mod+ (a b &optional (m +mod+))
  (declare (type (signed-byte 61) a b) (type %modulus m))
  (mod (+ a b) m))

(defun mod- (a b &optional (m +mod+))
  (declare (type (signed-byte 61) a b) (type %modulus m))
  (mod (- a b) m))

(defun mod* (a b &optional (m +mod+))
  (declare (type fixnum a b) (type %modulus m))
  ;; 先に 0..m-1 に直しておくので、積は m^2 未満で fixnum に収まる
  (mod (* (mod a m) (mod b m)) m))

(defun mod-pow (a b &optional (m +mod+))
  (declare (type fixnum a) (type (integer 0 #.most-positive-fixnum) b) (type %modulus m))
  (let ((p (mod a m))
        (ans (mod 1 m)))
    (declare (type (integer 0 (2147483648)) p ans))
    (loop while (> b 0)
          do (when (logbitp 0 b)
               (setf ans (mod (* ans p) m)))
             (setf p (mod (* p p) m))
             (setf b (ash b -1)))
    ans))

(defun mod-inv (a &optional (m +mod+))
  (declare (type fixnum a) (type %modulus m))
  (mod-pow a (- m 2) m))

(defun mod-div (a b &optional (m +mod+))
  (declare (type fixnum a b) (type %modulus m))
  (mod* a (mod-inv b m) m))

;;; ───────── 二項係数(表を使う版) ─────────

(sb-ext:defglobal *mod-fact*     (make-array 1 :element-type 'fixnum :initial-element 1))
(sb-ext:defglobal *mod-inv-fact* (make-array 1 :element-type 'fixnum :initial-element 1))
(declaim (type (simple-array fixnum (*)) *mod-fact* *mod-inv-fact*))

(defun init-fact (max-n)
  (declare (type (integer 0 #.(1- array-dimension-limit)) max-n))
  (let ((f  (make-array (1+ max-n) :element-type 'fixnum))
        (fi (make-array (1+ max-n) :element-type 'fixnum)))
    (declare (type (simple-array fixnum (*)) f fi))
    ;; f[i] = i!
    (setf (aref f 0) 1)
    (loop for i of-type fixnum from 1 to max-n
          do (setf (aref f i) (mod* (aref f (1- i)) i)))
    ;; fi[max-n] だけ逆元を計算し、そこから 1/(i-1)! = 1/i! * i で下ろしていく
    (setf (aref fi max-n) (mod-inv (aref f max-n)))
    (loop for i of-type fixnum from max-n downto 1
          do (setf (aref fi (1- i)) (mod* (aref fi i) i)))
    (setf *mod-fact* f
          *mod-inv-fact* fi)
    nil))

(declaim (inline fact inv-fact ncr npr nhr))

(defun fact (n)
  (declare (type fixnum n))
  (aref *mod-fact* n))

(defun inv-fact (n)
  (declare (type fixnum n))
  (aref *mod-inv-fact* n))

(defun ncr (n r)
  (declare (type fixnum n r))
  (if (or (< r 0) (< n r))
      0
      (mod* (aref *mod-fact* n)
            (mod* (aref *mod-inv-fact* r) (aref *mod-inv-fact* (- n r))))))

(defun npr (n r)
  (declare (type fixnum n r))
  (if (or (< r 0) (< n r))
      0
      (mod* (aref *mod-fact* n) (aref *mod-inv-fact* (- n r)))))

(defun nhr (n r)
  (declare (type fixnum n r))
  (cond ((< r 0) 0)
        ((= r 0) 1)                     ; 何も選ばない方法は 1 通り(n = 0 でも)
        (t (ncr (+ n r -1) r))))

;;; ───────── 二項係数(n が大きい版) ─────────

(defun ncr-large (n r &optional (m +mod+))
  (declare (type fixnum n r) (type %modulus m))
  (if (or (< r 0) (< n r))
      0
      (let ((k (min r (- n r)))
            (num 1)
            (den 1))
        (declare (type fixnum k) (type (integer 0 (2147483648)) num den))
        ;; num = n(n-1)…(n-k+1), den = k!
        ;; k < m なら den は m の倍数にならないので、割り算(逆元)が正しく使える。
        ;; n >= m で num が 0 になっても、そのときは nCr も m の倍数なので 0 で正しい。
        (loop for i of-type fixnum from 0 below k
              do (setf num (mod* num (- n i) m)
                       den (mod* den (1+ i) m)))
        (mod-div num den m))))

;;; ───────── 等比数列の和 ─────────

(defun mod-geometric-sum (a1 r n &optional (m +mod+))
  (declare (type fixnum a1 r) (type (integer 0 #.most-positive-fixnum) n)
           (type %modulus m))
  (if (= (mod r m) 1)
      (mod* a1 n m)                     ; 公比 1: a1 * n(n は先に mod を取ってから掛ける)
      (mod-div (mod* a1 (mod- (mod-pow r n m) 1 m) m)
               (mod- r 1 m)
               m)))
