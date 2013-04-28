#lang racket/base
(provide (all-defined-out))

(define current-level
  16)

(define compendium
  `(["Izanagi" 2144]
    ["Orobas" 2961]
    ["Pixie" 2169]
    ["Omoikane" 2784]
    ["Nata Taishi" 2625]
    ["Slime" 2169]
    ["Archangel" 4304]
    ["Angel" 2361]
    ["Valkyrie" 3296]
    ["Sandman" 2484]
    ["Apsaras" 2361]
    ["Ukobach" 2144]
    ["Titan" 4916]
    ["Sylph" 3764]
    ["Jack Frost" 5600]
    ["Cu Sith" 4025]))

(define active
  `("Titan"
    "Cu Sith"
    "Jack Frost"
    "Omoikane"))
