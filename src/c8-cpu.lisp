(in-package :c8-cpu)
(defparameter *mem-size* 4096)
(defparameter *load-addr* #x0200)
(defparameter *avail-mem* (- *mem-size* *load-addr*))

(deftype u8 () '(unsigned-byte 8))
(deftype u16 () '(unsigned-byte 16))

(defclass chip8 ()
    ((mem
       :initarg :mem
       :initform (make-array *mem-size* :element-type 'u8 :initial-element #x00)
       :accessor mem
       :documentation "Chip-8 memory")
     (registers
       :initarg :registers
       :initform (make-array 16 :element-type 'u8 :initial-element #x00)
       :accessor registers
       :documentation "16 8-bit general purpose registers")
     (I
       :initarg I
       :initform #x0000
       :type u16
       :accessor I
       :documentation "The 16-bit I register")
     (dt
       :initarg :dt
       :initform #x00
       :type u8
       :accessor dt
       :documentation "The 8-bit delay timer register")
     (st
       :initarg :st
       :initform #x00
       :type u8
       :accessor st
       :documentation "The 8-bit sound timer register")
     (pc
       :initarg :pc
       :initform #x0200
       :type u16
       :accessor pc
       :documentation "16-bit program counter register")
     (sp
       :initarg :sp
       :initform #x00
       :type u8
       :accessor sp
       :documentation "8-bit stack pointer")
     (stack
       :initarg :stack
       :initform (make-array 16 :element-type 'u16 :initial-element #x0000)
       :accessor stack
       :documentation "Stack of 16-bit values")
     (display
       :initarg :display
       :initform (make-array '(64 32) :element-type 'u8 :initial-element #x01)
       :accessor display
       :documentation "The Chip-8 display")))

(defun load-rom (cpu rom)
  (dotimes (off (min (length rom) *avail-mem*))
    (setf (aref (mem cpu) (+ off *load-addr*)) (aref rom off))))

(defun clear-user-mem (cpu)
  (dotimes (i *avail-mem*) (setf (aref (mem cpu) (+ i *load-addr*)) 0)))

(defun clear-registers (cpu)
  (dotimes (i (length (registers cpu)))
    (setf (aref (registers cpu) i) #x00)))

(defun reset (cpu)
  (clear-user-mem cpu)
  (clear-registers cpu)
  (setf (pc cpu) *load-addr*))

(defun clear-display (cpu)
  (destructuring-bind (n m) (array-dimensions (display cpu))
    (dotimes (i n)
      (dotimes (j m)
        (setf (aref (display cpu) i j) #x00)))))

(defun fetch (cpu)
  (when (<= (pc cpu) (- *mem-size* 2))
        (let ((seq (subseq (mem cpu) (pc cpu) (+ 2 (pc cpu)))))
          (incf (pc cpu) 2)
          seq)))

(defun run (cpu rom)
  (load-rom cpu rom)
  (loop for instr = (fetch cpu)
        for high-nib = (and instr (nib 1 (aref instr 0)))
        do (case high-nib
             ;; clear screen
             ((#x0) (case (nib 0 (aref instr 0))
                      ((#x0) (when (= #xE0 (aref instr 1))
                                   (clear-display cpu)))))
             ;; jump
             ((#x1) (setf (pc cpu) (dpb (nib 0 (aref instr 0))
                                        (byte 4 8)
                                        (aref instr 1))))
             ((#x2) (format t "0x~x, ~a~%" high-nib instr))
             ((#x3) (format t "0x~x, ~a~%" high-nib instr))
             ((#x4) (format t "0x~x, ~a~%" high-nib instr))
             ((#x5) (format t "0x~x, ~a~%" high-nib instr))
             ;; set Vx to NN
             ((#x6) (let ((reg (nib 0 (aref instr 0)))
                          (val (aref instr 1)))
                      (setf (aref (registers cpu) reg) val)))
             ;; add NN to Vx and store in Vx
             ;; TODO: on overflow?
             ((#x7) (let* ((reg (nib 0 (aref instr 0)))
                           (nn (aref instr 1))
                           (rv (aref (registers cpu) reg)))
                      (setf (aref (registers cpu) reg) (+ rv nn))))
             ((#x8) (format t "0x~x, ~a~%" high-nib instr))
             ((#x9) (format t "0x~x, ~a~%" high-nib instr))
             ;; Set I reg to NNN
             ((#xA) (let ((nib2 (nib 0 (aref instr 0)))
                          (nib01 (aref instr 1)))
                      (setf (I cpu) (+ (ash nib2 8) nib01))))
             ((#xB) (format t "0x~x, ~a~%" high-nib instr))
             ((#xC) (format t "0x~x, ~a~%" high-nib instr))
             ;; Dxyn
             ;; read n bytes, starting at I
             ;; display on screen at xy
             ((#xD) (let* ((x (nib 0 (aref instr 0)))
                           (y (nib 1 (aref instr 1)))
                           (n (nib 0 (aref instr 1)))
                           (addr (I cpu))
                           (sprite (subseq (mem cpu) addr n)))
                      )))
          ((#xE) (format t "0x~x, ~a~%" high-nib instr))
          ((#xF) (format t "0x~x, ~a~%" high-nib instr))
          ((nil) (format t "done") (return))
          (t (format t "else: 0x~2,'0x0x~2,'0x~%" (aref instr 0) (aref instr 1))))))

(defun nib (loc n)
  (ldb (byte 4 (* loc 4)) n))

;; scratch
(format t "bin: ~b" (dpb #xFF (byte 8 8) 0))
(dpb #xFF (byte 8 8) 0)
(ldb (byte 3 1) #b1101)
(format t "~b" #xFFF)
(defparameter *cpu* (make-instance 'chip8))
(load-rom *cpu* #(#x00 #xE0 #x1A #xA0))
(reset *cpu*)
(subseq (mem *cpu*) *load-addr* (+ 6 *load-addr*))
(run *cpu* #(#xAF #x0F))
(reset *cpu*)
(format t "~b" (I *cpu*))
(registers *cpu*)
(setf (pc *cpu*) 512)
(format t "~x~%" 250)
(pc *cpu*)
(apropos 'byte)
(Describe 'unsigned-byte)

(format t "0x~x" (+ #x80 #x02))
(format t "~d" #x8002)