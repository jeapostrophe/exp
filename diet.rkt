#lang racket/base

(define Categories
  '([Meat
     (Beef Lamb Pork Chicken)]
    [Fish
     (Salmon Trout Haddock)]
    [Eggs
     (Omega-3 Pastured-Eggs)]
    [Veggies
     ;; http://lowcarbdiets.about.com/od/whattoeat/a/whatveg.htm
     (Spinach Broccoli Cauliflower Carrots Greens Peppers Onions)]
    [Fruits
     (Apples Oranges Pears Blueberries Strawberries)]
    [Nuts-and-Seeds
     (Almonds Walnuts Sunflower-seeds)]
    [High-fat-Dairy
     (Cheese Butter Heavy-Cream Yogurt)]))

;; Don't have too many nuts or cheese
;; 1 piece of fruit per day

(define Snacks
  '([Piece of Fruit]
    [Pork-rinds]
    [Advocado]
    [Full-fat Yogurt]
    [Hard-boiled Egg or Two]
    [Baby carrots]
    [Handful of Nuts]
    [Some cheese and meat]))

(define Plans
  '([Monday
     ([Breakfast
       (Omelet with veggies fried in butter)]
      [Lunch
       (Grass-fed yogurt with blueberries & handful of almonds)]
      [Dinner
       (Cheeseburger (no bun) served with veggies)])]
    [Tuesday
     ([Breakfast
       (Bacon and eggs)]
      [Lunch
       (Leftover burgers and veggies)]
      [Dinner
       (Salmon with butter and veggies)])]
    [Wednesday
     ([Breakfast
       (Eggs and veggies fried in butter)]
      [Lunch
       (Shrimp salad with some olive oil)]
      [Dinner
       (Grilled chicken with veggies)])]
    [Thursday
     ([Breakfast
       (Omelet with veggies fried in butter)]
      [Lunch
       (Smoothie with coconut milk, berries, almonds, and protein powder)]
      [Dinner
       (Steak and veggies)])]
    [Friday
     ([Breakfast
       (Bacon and eggs)]
      [Lunch
       (Chicken salad with some olive oil)]
      [Dinner
       (Pork chops with veggies)])]
    [Saturday
     ([Breakfast
       (Omelet with veggies fried in butter)]
      [Lunch
       (Grass-fed yogurt with berries, coconut flakes, & handful of walnuts)]
      [Dinner
       (Meatballs with veggies)])]
    [Sunday
     ([Breakfast
       (Bacon and eggs)]
      [Lunch
       (Smoothie with coconut milk, heavy cream, chocolate protein powder and berries)]
      [Dinner
       (Grilled chicken wings with some raw spinach on the side)])]))
