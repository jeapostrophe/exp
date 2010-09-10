#lang racket
(define rom-p
  "/Users/jay/Downloads/nes-roms.txt")

(define rom-paths
  (file->lines rom-p))

(define (find&remove s rx)
  (define new-s (regexp-replace (format " *~a *" rx) s " "))
  (if (string=? s new-s)
      (values s #f)
      (values new-s #t)))

(define (record-update p . attrs)
  (λ (ht)
    (let loop ([ht ht] [attrs attrs])
      (match attrs
        [(list) ht]
        [(list-rest has-attr? attr attrs)
         (loop (if has-attr?
                   (hash-set ht attr p)
                   ht)
               attrs)]))))

(define (rename rom ht)
  (hash-ref ht rom rom))

(define roms
  (for/fold ([roms (hash)])
    ([p (in-list rom-paths)])
    (let*-values
        ([(p rom ext)
          (apply values (regexp-match #rx"^(.+)\\.(nes|unf|NES)$" p))]
         [(rom has-!?)
          (find&remove rom (regexp-quote "[!]"))]
         [(rom has-J?)
          (find&remove rom (regexp-quote "(J)"))]
         [(rom has-E?)
          (find&remove rom (regexp-quote "(E)"))]
         [(rom has-Unl?)
          (find&remove rom (regexp-quote "(Unl)"))]
         [(rom has-U?)
          (find&remove rom (regexp-quote "(U)"))]
         [(rom has-U/bracket?)
          (find&remove rom (regexp-quote "[U]"))]
         [(rom has-JU?)
          (find&remove rom (regexp-quote "(JU)"))]
         [(rom has-UE?)
          (find&remove rom (regexp-quote "(UE)"))]
         [(rom has-JUE?)
          (find&remove rom (regexp-quote "(JUE)"))]
         [(rom has-JE?)
          (find&remove rom (regexp-quote "(JE)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(As)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(A)"))]
         [(rom has-PC10?)
          (find&remove rom (regexp-quote "(PC10)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(PD)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(G)"))]
         [(rom has-PRG2?)
          (find&remove rom (regexp-quote "(PRG2)"))]
         [(rom has-PRG1?)
          (find&remove rom (regexp-quote "(PRG1)"))]
         [(rom has-PRG0?)
          (find&remove rom (regexp-quote "(PRG0)"))]
         [(rom has-PRG0CHR1?)
          (find&remove rom (regexp-quote "(PRG0 CHR1)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(Prototype)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(Chinese)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(Russian)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(Sachen)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(VS)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(PAL)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(GC)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(SW)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(FC)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(F)"))]
         [(rom _)
          (find&remove rom (regexp-quote "[t1]"))]
         [(rom _)
          (find&remove rom (regexp-quote "[t2]"))]
         [(rom _)
          (find&remove rom (regexp-quote "[f1]"))]
         [(rom _)
          (find&remove rom (regexp-quote "(HES)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(KC)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(I)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(Aladdin)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(Tengen)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(Joy Van)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(Unreleased)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(Taito)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(Namco)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(Victor)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(Bootleg)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(UBI Soft)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(Player 2 Mode)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(Player 1 Mode)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(Dr. PC Jr.)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(NG-Dump Known)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(Beta)"))]
         [(rom _)
          (find&remove rom (regexp-quote "(Mindscape)"))]
         [(_rom rom t-string)
          (cond
            [(regexp-match #rx"^(.+) \\[(T.+)\\]$" rom)
             => (λ (m) (apply values m))]
            [else
             (values #f rom "")])]
         [(rom)
          (regexp-replace #rx" +$" rom "")]
         [(rom)
          (rename 
           rom
           (hash
            "Um Chi (Glommy Chess)" "Glommy Chess"
            "Shisen Mahjong - Seifuku Hen (Regular Edition)" #f
            "Zhong Guo Xiang Qi (Chinese Cheese)" "Chinese Cheese"
            "Stack Up (Robot Block)" "Stack Up"
            "BAPSACRSTRKCGTF (Demo Phase 2) (AKA B00daw's Folly)" #f
            "BAPSACRSTRKCGTF (Demo Phase 1) (AKA B00daw's Folly)" #f
            "NES Test Cart (Official Nintendo)" "NES Test Cart"
            "Moero!! Pro Yakyuu (Red)" "Moero!! Pro Yakyuu - Red"
            "Moero!! Pro Yakyuu (Black)" "Moero!! Pro Yakyuu - Black"
            "Hyper Olympic (Genteiban!)" "Hyper Olympic - Genteiban!"
            "Tank Demo (Mapper 0 NTSC)" "Tank Demo"
            "Tank Demo (Mapper 1 NTSC)" "Tank Demo"
            "Tank Demo (Mapper 0 PAL)" "Tank Demo"
            "Tank Demo (Mapper 1 PAL)" "Tank Demo"
            "Mac OS Demo (Small)" #f
            "Mac OS Demo (Large)" "Mac OS Demo"
            "Gradius (ArchiMENdes Hen)" #f
            "Chinese Odyssey, A (AKA Da Hua Xi You)" "Chinese Odyssey, A"
            "Wa Di Lei (Minesweeper)" "Minesweeper"
            "Pro Action Replay (No Cart Present)" "Pro Action Replay - No Cart Present"
            "Game II (Version B)" "Game II"
            "Tetramino (20031101) (0.1) by Damian Yerrick" "Tetramino"
            "Tetramino (20031217) (0.2) by Damian Yerrick" "Tetramino"
            "Takeshi no Chousenjou (1986)" "Takeshi no Chousenjou - 1986"
            "Twin Eagle (Shuang Ying)" "Twin Eagle"
            "Spiritual Warfare (V6.1)" "Spiritual Warfare"
            "Spiritual Warfare (V6.0)" "Spiritual Warfare"
            "Mari - Ayami - Luka no AV Poker (Pu Nu Jing Ling)" "Mari - Ayami - Luka no AV Poker - Pu Nu Jing Ling"
            "Quattro Sports (V3 Plug-Thru Cart)" "Quattro Sports"
            "Family BASIC (V2.1a)" #f
            "Family BASIC (V2.0a)" #f
            "Family BASIC (V3.0)" "Family BASIC"
            "Playbox BASIC (Prototype V0.0)" "Playbox BASIC"
            "Little Red Hood (Xiao Hong Mao)" "Little Red Hood"
            "PasoFami Demo 2 (TwinBee)" #f
            "Sheng Hen Pao (AKA Twin Loud Cannon)" "Twin Loud Cannon"
            "Mouser (Beta 1.0)" "Mouser"
            "Barbie (Rev 3)" #f
            "Barbie (Rev X)" "Barbie"
            "Nintendo World Cup (Rev 3)" "Nintendo World Cup"
            "Yie Ar Kung-Fu (V1.2)" #f
            "Yie Ar Kung-Fu (V1.4)" "Yie Ar Kung-Fu"
            "King of Kings, The (V1.1)" #f
            "King of Kings, The (V1.2)" #f
            "King of Kings, The (V1.3)" #f
            "King of Kings, The (V5.0 CHR 1.3)" "King of Kings, The"
            "Pro Action Replay (Rev B)" "Pro Action Replay - Rev B"
            "Mei Nu Quan (Honey Peach)" "Honey Peach"
            "Joshua (V5.0 CHR 6.0)" #f
            "Joshua (V6.0)" "Joshua"
            "Best Play Pro Yakyuu (Shin Data)" "Best Play Pro Yakyuu - Shin Data"
            "Super 40-in-1 (Multicart WS-1001)" "Super 40-in-1"
            "Bible Adventures (V1.2)" #f
            "Bible Adventures (V1.3)" "Bible Adventures"
            "Double Strike (V1.1)" "Double Strike"
            "Double Strike (V1.0)" #f
            "Exodus (V4.0)" "Exodus"
            "Takeshi no Chousenjou (1990)" "Takeshi no Chousenjou - 1990"
            "Metal Fighter (Wei Lai Xiao Zi)" "Metal Fighter"
            "NES Scrolling Test by Lasse Oorni (Cadaver)" "NES Scrolling Test"
            "NES Sound Test by Lasse Oorni (Cadaver)" "NES Sound Test"
            "Side Winder (Xiang Wei She)" "Side Winder"
            "Dong Dong Nao II - Guo Zhong Ying Wen (Middle School English II)" "Dong Dong Nao II - Guo Zhong Ying Wen"
            "Shisen Mahjong - Seifuku Hen (Uniform Edition)" "Shisen Mahjong - Seifuku Hen"
            "Bao Xiao Tien Guo (Explosion Sangokushi)" "Explosion Sangokushi"
            "Doctor PC Jr. - Xue Si Dian Nao (Part 2)" "Xue Si Dian Nao - Part 2"
            "Doctor PC Jr. - Xue Si Dian Nao (Part 1)" "Xue Si Dian Nao - Part 1"))])      
      
      (if rom
          (hash-update roms rom
                       (record-update 
                        p
                        (regexp-match #rx"^T\\+Eng" t-string) 'T+Eng
                        (regexp-match #rx"^T\\-Eng" t-string) 'T-Eng
                        (not (string=? "" t-string)) 'T???
                        (or has-PRG0CHR1? has-PRG0?) 'PRG0
                        has-PRG1? 'PRG1
                        has-PRG2? 'PRG2
                        has-PC10? 'PC10
                        has-!? '!
                        (or has-J? has-JU? has-JUE? has-JE?) 'J
                        (or has-E? has-UE? has-JUE? has-JE?) 'E
                        has-Unl? 'Unl
                        (or has-U? has-UE? has-U/bracket? has-JU? has-JUE?) 'U)
                       (hasheq))
          roms))))

(define Priority
  '(T+Eng T-Eng U J E Unl !))

(for ([(name attr->path) (in-hash roms)])
  (when (regexp-match (string-append "[" (regexp-quote "([") "]") name)
    (error 'rom-sort "Rom with left-overs: ~e" name))
  (define best
    (for/or ([a (in-list Priority)])
      (hash-ref attr->path a #f)))
  (when best
    (printf "ln -s ~S ~S\n" (format "$(pwd)/~a" best) (format "../Roms/~a.nes" name))))