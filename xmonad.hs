import XMonad
import XMonad.Hooks.DynamicLog
import XMonad.Hooks.ManageDocks
import XMonad.Util.Run(spawnPipe)
import XMonad.Util.EZConfig
import System.IO
import qualified XMonad.StackSet as W

main = do
  xmproc <- spawnPipe "exec xmobarj ~/.xmobarrc"
  xmonad $ defaultConfig
       { manageHook = manageDocks <+> manageHook defaultConfig,
         layoutHook = avoidStruts $ layoutHook defaultConfig,
         logHook = dynamicLogWithPP xmobarPP
                   { ppOutput = hPutStrLn xmproc,
                     ppCurrent = xmobarColor "#cb4b16" "" . wrap "[" "]",
                     ppTitle = xmobarColor "#93a1a1" "" . shorten 70 },
         modMask = mod4Mask,
         borderWidth = 1,
         terminal = "urxvtc -e screen -UxS lightning",
         normalBorderColor = "#ffffff",
         focusedBorderColor = "#073642" }
       `additionalKeysP`
       [ ("M4-;", spawn "jpn-on"),
         ("M4-'", spawn "jpn-off"),
         ("M4-S-z", spawn "gnome-screensaver-command --lock"),
         ("M4-<Space>", spawn "exec dmenu.sh"),
         ("M4-`", sendMessage NextLayout),
         ("M4-S-w", spawn "exec conkeror -new chrome://"),
         ("M4-S-e", spawn "exec emacsclient -nc"),
         ("M4-S--", sendMessage Shrink),
         ("M4-S-=", sendMessage Expand),
         ("M4-S-t", withFocused $ windows . W.sink),
         ("M4-<Esc>", spawn "xmonad --recompile && xmonad --restart")
       ]
       `removeKeysP`
       [ "M4-r", "M4-n", "M4-w", "M4-p", "M4-q", "M4-t", "M4-l", "M4-h", "M4-S-q" ]
                                          
