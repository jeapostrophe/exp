#lang racket/base

(define arcana
  '(Fool Magician Priestess Empress Emperor Hierophant Lovers Chariot Justice Hermit Fortune Strength Hanged-Man Death Temperance Devil Tower Star Moon Sun Judgement Jester Aeon))

(define fusion-chart
  ;; This is column order
  '([Fool Fortune Lovers Judgement Hermit Tower Devil Lovers Chariot Strength Judgement Empress Star Star Justice Lovers Fortune Hermit Empress Empress Temperance Priestess Jester]
    [Temperance Magician Fortune Sun Death Jester Temperance Emperor Chariot Empress Strength Tower Fortune Fool Sun Chariot Emperor Hierophant Sun Fortune Sun Star Empress]
    [Death Moon Priestess Temperance Justice Empress Hanged-Man Magician Hermit Magician Aeon Empress Chariot Chariot Lovers Hermit Moon Empress Empress Aeon Temperance Moon Fool]
    [Moon Justice Hermit Empress Fool Priestess Fool Emperor Death Fool Strength Jester Sun Hierophant Aeon Fool Judgement Jester Moon Lovers Star Devil Star]
    [Death Strength Empress Moon Emperor Chariot Devil Tower Jester Moon Priestess Hermit Hierophant Strength Devil Death Priestess Sun Strength Devil Hanged-Man Chariot Sun]
    ;; XXX Hierophant
    ))
