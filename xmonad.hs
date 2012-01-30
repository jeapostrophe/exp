import XMonad
import XMonad.Hooks.DynamicLog
import XMonad.Hooks.ManageDocks
import XMonad.Util.Run(spawnPipe)
import XMonad.Util.EZConfig
import System.IO
import qualified XMonad.StackSet as W

main = do
  xmproc <- spawnPipe "exec xmobar ~/.xmobarrc"
  xmonad $ defaultConfig
       { manageHook = manageDocks <+> manageHook defaultConfig,
         layoutHook = avoidStruts $ layoutHook defaultConfig,
         logHook = dynamicLogWithPP xmobarPP
                   { ppOutput = hPutStrLn xmproc,
                     ppTitle = xmobarColor "white" "" . shorten 70 },
         modMask = mod4Mask,
         borderWidth = 2,
         terminal = "urxvtc -e screen -UxS lightning",
         normalBorderColor = "#cccccc",
         focusedBorderColor = "#cd8b00" }
       `additionalKeysP`
       [ ("M4-S-z", spawn "gnome-screensaver-command --lock"),
         ("M4-<Space>", spawn "exec dmenu_run"),
         ("M4-`", sendMessage NextLayout),
         ("M4-S-w", spawn "exec conkeror -new chrome://"),
         ("M4-S-e", spawn "exec emacsclient -nc"),
         ("M4-S-t", withFocused $ windows . W.sink),
         ("M4-<Esc>", spawn "xmonad --recompile && xmonad --restart")
       ]
       `removeKeysP`
       [ "M4-r", "M4-n", "M4-w", "M4-p", "M4-q", "M4-t", "M4-l", "M4-h" ]
                                          
