#lang at-exp racket/base
(require racket/match
         racket/string
         racket/format
         ffi/vector
         opengl)

;; This is mostly copied from Mode-λ, but simplified

(define-syntax-rule (with-texture (GL_TEXTUREx TextureId) body ...)
  (let ()
    (glActiveTexture GL_TEXTUREx)
    (glBindTexture GL_TEXTURE_2D TextureId)
    body ...
    (glActiveTexture GL_TEXTUREx)
    (glBindTexture GL_TEXTURE_2D 0)))

;; Copied from opengl (and sgl)
(define (argb->rgba! pixels)
  (for ((i (in-range (/ (bytes-length pixels) 4))))
    (let* ((offset (* 4 i))
           (alpha (bytes-ref pixels (+ 0 offset)))
           (  red (bytes-ref pixels (+ 1 offset)))
           (green (bytes-ref pixels (+ 2 offset)))
           ( blue (bytes-ref pixels (+ 3 offset))))
      (bytes-set! pixels (+ 0 offset) red)
      (bytes-set! pixels (+ 1 offset) green)
      (bytes-set! pixels (+ 2 offset) blue)
      (bytes-set! pixels (+ 3 offset) alpha))))

;; These helpers are very busy for getting good errors when the
;; shaders break. It is very unlikely these shaders will ever break.
(define (print-shader-log glGetShaderInfoLog shader-name shader-id shader-source)
  (define-values (infoLen infoLog)
    (glGetShaderInfoLog shader-id 1024))
  (unless (zero? infoLen)
    (eprintf "Log of shader(~a):\n" shader-name)
    (define real-log (bytes->string/utf-8 (subbytes infoLog 0 infoLen)))
    (define shader-lines (string-split shader-source "\n"))
    (for ([l (in-list (string-split real-log "\n"))])
      (eprintf "\t~a\n" l)
      (match (regexp-match #rx"^0\\(([0-9]*?)\\) : " l)
        [(list _ ns)
         (eprintf "\t\t=> ~a\n"
                  (list-ref shader-lines (sub1 (string->number ns))))]
        [_
         (void)]))
    (eprintf "Shader source follows:\n~a\n"
             shader-source)))

(define (compile-shader GL_VERTEX_SHADER ProgramId VertexShader)
  (define VertexShaderId (glCreateShader GL_VERTEX_SHADER))
  (glShaderSource VertexShaderId 1
                  (vector
                   (string-append
                    (format "#version ~a\n"
                            ;; XXX This is likely to be a problem in Wayland
                            (match '3.3
                              ['3.3 "330 core"]
                              ['es3.1 "310 es"]))
                    VertexShader))
                  (s32vector))
  (glCompileShader VertexShaderId)
  (unless (= GL_TRUE (glGetShaderiv VertexShaderId GL_COMPILE_STATUS))
    (print-shader-log glGetShaderInfoLog ProgramId VertexShaderId VertexShader)
    (error 'compile-shader "failed to compile ~a shader ~v"
           (if (= GL_FRAGMENT_SHADER GL_VERTEX_SHADER)
             "fragment"
             "vertex")
           ProgramId))
  (glAttachShader ProgramId VertexShaderId))

(define (glLinkProgram&check ProgramId ProgramName)
  (glLinkProgram ProgramId)
  (unless (= GL_TRUE (glGetProgramiv ProgramId GL_LINK_STATUS))
    (print-shader-log glGetProgramInfoLog ProgramId ProgramId "[inside linking]")
    (error 'glLinkProgram&check "failed to link program ~v" ProgramId))
  (glValidateProgram ProgramId)
  (unless (= GL_TRUE (glGetProgramiv ProgramId GL_VALIDATE_STATUS))
    (print-shader-log glGetProgramInfoLog ProgramId ProgramId "[during validation]")
    (error 'glLinkProgram&check "failed to validate program ~v" ProgramName)))

(define (make-draw bm-w bm-h bm-bs)
  (define (glGen glGenThing)
    (u32vector-ref (glGenThing 1) 0))
  
  (define bm-tex (glGen glGenTextures))
  (with-texture (GL_TEXTURE0 bm-tex)
    (glTexParameteri GL_TEXTURE_2D GL_TEXTURE_MIN_FILTER GL_NEAREST)
    (glTexParameteri GL_TEXTURE_2D GL_TEXTURE_MAG_FILTER GL_NEAREST)
    (glTexParameteri GL_TEXTURE_2D GL_TEXTURE_WRAP_S GL_CLAMP_TO_EDGE)
    (glTexParameteri GL_TEXTURE_2D GL_TEXTURE_WRAP_T GL_CLAMP_TO_EDGE)
    (argb->rgba! bm-bs)
    (glTexImage2D GL_TEXTURE_2D
                  0 GL_RGBA
                  bm-w bm-h 0
                  GL_RGBA GL_UNSIGNED_BYTE
                  bm-bs))

  (define bm-vao (glGen glGenVertexArrays))
  (define bm-program (glCreateProgram))

  (define bm-vert
    @~a{
out vec2 texCoord;

const vec2 full_coordData[4] =
vec2[4]( vec2(0.0, 1.0),
         vec2(0.0, 0.0),
         vec2(1.0, 1.0),
         vec2(1.0, 0.0) );
const vec2 center_coordData[4] =
vec2[4]( vec2(-1.0, +1.0),
         vec2(-1.0, -1.0),
         vec2(+1.0, +1.0),
         vec2(+1.0, -1.0) );
    
void main() {
 gl_Position = vec4( center_coordData[ gl_VertexID ].xy, 0.0, 1.0 );
 texCoord = full_coordData[ gl_VertexID ];
}})
  (define bm-fragment
    @~a{
uniform sampler2D BitmapTex;
in vec2 texCoord;
out vec4 oFragColor;

void main() {
 oFragColor = texture(BitmapTex, texCoord);
}})

  (compile-shader GL_VERTEX_SHADER bm-program bm-vert)
  (compile-shader GL_FRAGMENT_SHADER bm-program bm-fragment)

  (glBindVertexArray bm-vao)
  (glLinkProgram&check bm-program 'bm)
  (glUseProgram bm-program)
  (glUniform1i (glGetUniformLocation bm-program "BitmapTex") 0)
  (glUseProgram 0)
  (glBindVertexArray 0)

  (λ (c-w c-h)
    (glUseProgram bm-program)
    (with-texture (GL_TEXTURE0 bm-tex)
      (glBindVertexArray bm-vao)
      (glClearColor 0.0 0.0 0.0 0.0)
      (glClear GL_COLOR_BUFFER_BIT)
      (glDrawArrays GL_TRIANGLE_STRIP 0 4))
    (glBindVertexArray 0)
    (glUseProgram 0)))

(module+ main
  (require racket/gui
           racket/class
           racket/draw
           framework)

  (define bm (icon:get-gc-on-bitmap))
  (define W (send bm get-width))
  (define H (send bm get-height))
  (define bs (make-bytes (* 4 W H)))
  (send bm get-argb-pixels 0 0 W H bs)

  (define draw #f)
  (define (paint-canvas c dc)
    (define-values (cw ch) (send c get-scaled-client-size))
    (define gl-ctx (send dc get-gl-context))
    (send gl-ctx
          call-as-current
          (λ ()
            (unless draw
              (set! draw (make-draw W H bs)))
            (draw cw ch)
            (send gl-ctx swap-buffers))))

  (define gl-conf (new gl-config%))
  (send gl-conf set-legacy? #f)

  (define f (new frame% [label "GL Bitmap"] [width W] [height H]))
  (define c
    (new canvas%
         [parent f]
         [min-width W]
         [min-height H]
         [gl-config gl-conf]
         [style '(no-autoclear gl)]
         [paint-callback paint-canvas]))

  (send f show #t))
