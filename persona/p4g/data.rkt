#lang racket/base
(module+ test
  (require rackunit))

(define arcana
  '(Fool Magician Priestess Empress Emperor Hierophant Lovers Chariot Justice Hermit Fortune Strength Hanged-Man Death Temperance Devil Tower Star Moon Sun Judgement Jester Aeon))

;; Based on: http://www.gamefaqs.com/vita/641695-persona-4-golden/faqs/64587
(define fusion-chart
  ;; This is column order
  '([Fool Fortune Lovers Judgement Hermit Tower Devil Lovers Chariot Strength Judgement Empress Star Star Justice Lovers Fortune Hermit Empress Empress Temperance Priestess Jester]
    [Temperance Magician Fortune Sun Death Jester Temperance Emperor Chariot Empress Strength Tower Fortune Fool Sun Chariot Emperor Hierophant Sun Fortune Sun Star Empress]
    [Death Moon Priestess Temperance Justice Empress Hanged-Man Magician Hermit Magician Aeon Empress Chariot Chariot Lovers Hermit Moon Empress Empress Aeon Temperance Moon Fool]
    [Moon Justice Hermit Empress Fool Priestess Fool Emperor Death Fool Strength Jester Sun Hierophant Aeon Fool Judgement Jester Moon Lovers Star Devil Star]
    [Death Strength Empress Moon Emperor Chariot Devil Tower Jester Moon Priestess Hermit Hierophant Strength Devil Death Priestess Sun Strength Devil Hanged-Man Chariot Sun]
    ;; Hierophant
    [Chariot Devil Sun Death Empress Hierophant Hanged-Man Judgement Magician Lovers Hanged-Man Moon Star Magician Emperor Moon Emperor Lovers Aeon Magician Fool Fortune Sun]
    [Empress Death Emperor Justice Justice Death Lovers Hierophant Aeon Hierophant Hanged-Man Fool Justice Hanged-Man Fortune Tower Judgement Hierophant Hanged-Man Jester Emperor Tower Judgement]
    [Sun Temperance Hierophant Justice Temperance Sun Hierophant Chariot Temperance Priestess Temperance Aeon Devil Devil Moon Emperor Hierophant Aeon Fool Priestess Tower Strength Justice]
    [Magician Strength Hermit Magician Devil Temperance Priestess Temperance Justice Emperor Priestess Priestess Star Devil Magician Priestess Chariot Sun Star Judgement Sun Hermit Temperance]
    [Strength Empress Death Magician Priestess Justice Magician Justice Strength Hermit Judgement Justice Strength Magician Devil Death Jester Death Jester Tower Temperance Aeon Moon]
    [Magician Lovers Hanged-Man Star Lovers Priestess Star Devil Lovers Empress Fortune Priestess Fool Moon Tower Tower Magician Magician Strength Chariot Fool Empress Fool]
    ;; Strength
    [Magician Justice Justice Hierophant Hermit Sun Emperor Magician Temperance Hierophant Star Strength Star Empress Emperor Lovers Devil Devil Hierophant Tower Temperance Magician Hermit]
    [Strength Sun Moon Temperance Empress Death Moon Death Priestess Moon Death Hierophant Hanged-Man Devil Justice Justice Fortune Sun Magician Empress Fortune Moon Jester]
    [Hermit Emperor Magician Chariot Moon Devil Star Hermit Strength Sun Hermit Hanged-Man Priestess Death Jester Lovers Justice Fortune Hanged-Man Empress Strength Fortune Strength]
    [Hierophant Strength Hierophant Devil Sun Magician Hierophant Magician Hermit Magician Devil Sun Death Chariot Temperance Justice Judgement Hierophant Hanged-Man Fortune Chariot Priestess Judgement]
    ;; Devil
    [Temperance Sun Justice Priestess Moon Emperor Hierophant Moon Magician Justice Emperor Hermit Justice Star Hermit Devil Star Fortune Death Lovers Death Aeon Lovers]
    [Star Hanged-Man Magician Hermit Star Hanged-Man Star Hanged-Man Lovers Death Chariot Hanged-Man Hermit Lovers Star Emperor Tower Hermit Hanged-Man Death Aeon Judgement Fortune]
    [Empress #f Emperor Chariot Death Moon Hermit Hierophant Moon Justice Star Emperor Empress Lovers Hierophant Emperor Hanged-Man Star Death Chariot Lovers Death Tower]
    ;; Moon
    [Emperor Star Star Temperance Magician Emperor Hanged-Man Sun Strength Empress Lovers Justice Priestess Priestess Hanged-Man Empress Priestess Emperor Moon Death Hermit Hanged-Man Tower]
    [Devil Chariot Devil Priestess Chariot Strength Devil Strength Temperance Temperance Priestess Temperance Devil Empress Hermit Hierophant Chariot Moon Strength Sun Chariot Lovers Hierophant]
    [Hanged-Man Lovers Sun Priestess Lovers Chariot Strength Temperance Lovers Strength Hanged-Man #f Empress #f #f #f #f #f #f #f Judgement Death Sun]
    [Priestess Hierophant Devil Strength Justice Magician Sun Chariot Emperor Moon Devil Empress Priestess Temperance Death Chariot Hermit Empress Hermit Lovers Chariot Jester Judgement]
    [Death Emperor Sun Temperance Hanged-Man Moon Justice Strength Lovers
 Magician Priestess Chariot Death Hanged-Man Emperor Magician Emperor Chariot Hierophant Priestess Hanged-Man Death Aeon]))

(module+ test
  (for ([r (in-list fusion-chart)]
        [i (in-naturals)])
    ;; There is a diagonal with identity
    (check-equal? (list-ref r i)
                  (list-ref arcana i)                  
                  (format "row ~a has diagonal" i))
    ;; Every arcana is listed
    (check-equal? (length r)
                  (length arcana)
                  (format "row ~a is correct length" i))
    ;; Only contains arcana or #f
    (for ([e (in-list r)])
      (when e (check-not-false (member e arcana))))))
