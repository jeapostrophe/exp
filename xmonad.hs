import XMonad
import XMonad.Hooks.DynamicLog
import XMonad.Hooks.ManageDocks
import XMonad.Util.Run(spawnPipe)
import XMonad.Util.EZConfig
import Graphics.X11.ExtraTypes.XF86
import System.IO
import qualified Data.Map as M
import qualified XMonad.StackSet as W
import XMonad.Actions.GridSelect
import XMonad.Layout.WindowNavigation
import XMonad.Hooks.ManageHelpers
import XMonad.Hooks.EwmhDesktops

myWorkspaces = ["1", "2", "3", "4", "5", "6", "7", "8", "9", "0" ]

myNavigation :: TwoD a (Maybe a)
myNavigation = makeXEventhandler $ shadowWithKeymap navKeyMap navMyHandler
  where navKeyMap = M.fromList [
           ((0,xK_Escape)     , cancel)
          ,((0,xF86XK_LaunchA), cancel)
          ,((0,xF86XK_LaunchB), cancel)
          ,((0,xK_Return)     , select)
          ,((0,xK_slash)      , substringSearch myNavigation)
          ,((0,xK_Left)       , move (-1,0) >> myNavigation)
          ,((0,xK_Right)      , move (1,0) >> myNavigation)
          ,((0,xK_Down)       , move (0,1) >> myNavigation)
          ,((0,xK_Up)         , move (0,-1) >> myNavigation)
          ,((0,xK_BackSpace), transformSearchString (\s -> if (s == "") then "" else init s) >> myNavigation)         
          ]
        -- The navigation handler ignores unknown key symbols,
        -- therefore we const
        navMyHandler (_,s,_) = do
          transformSearchString (++ s)
          myNavigation

myGSConfig :: HasColorizer a => GSConfig a
myGSConfig = defaultGSConfig
  { gs_navigate = myNavigation
  }

myLayoutHook = wntiled ||| Mirror wntiled ||| Full
 where tiled = Tall nmaster delta ratio
       wntiled = windowNavigation tiled
       nmaster = 1
       ratio = 1/2
       delta = 3/100

main = do
  xmproc <- spawnPipe "exec xmobarj ~/.xmobarrc"
  xmonad $ ewmh defaultConfig
       { manageHook = manageDocks 
                  <+> manageHook defaultConfig,
         layoutHook = avoidStruts $ myLayoutHook,
         logHook = dynamicLogWithPP xmobarPP
                   { ppOutput = hPutStrLn xmproc,
                     ppHiddenNoWindows = xmobarColor "#dc322f" "",
                     ppCurrent = xmobarColor "#268bd2" "" . wrap "[" "]",
                     ppLayout = (\s -> if s == "Mirror Tall" then "Mall" else s),
                     ppWsSep = "",
                     ppSep = " ",
                     ppTitle = xmobarColor "#93a1a1" "" . shorten 70 . (\s -> ": " ++ s)},
         modMask = mod4Mask,
         borderWidth = 1,
         workspaces = myWorkspaces,
         focusFollowsMouse = False, 
         terminal = "urxvtc -e screen -UxS lightning",
         normalBorderColor = "#fdf6e3",
         focusedBorderColor = "#073642" } 
       `additionalKeys`
       [((m .|. mod4Mask, k), windows $ f i)
        | (i, k) <- zip myWorkspaces ([xK_1 .. xK_9] ++ [xK_0])
        , (f, m) <- [(W.greedyView, 0), (W.shift, shiftMask)]]
       `additionalKeysP`       
       [ ("M4-;", spawn "jpn-on"),
         ("M4-'", spawn "jpn-off"),
         ("M4-S-z", spawn "gnome-screensaver-command --lock"),
         ("M4-S-<Left>", sendMessage $ Swap L),
         ("M4-S-<Right>", sendMessage $ Swap R),
         ("M4-S-<Up>", sendMessage $ Swap U),
         ("M4-S-<Down>", sendMessage $ Swap D),
         ("M4-<Left>", sendMessage $ Go L),
         ("M4-<Right>", sendMessage $ Go R),
         ("M4-<Up>", sendMessage $ Go U),
         ("M4-<Down>", sendMessage $ Go D),
         ("M4-<Space>", spawn "exec dmenu.sh"),
         ("M4-`", sendMessage NextLayout),
         ("M4-S-w", spawn "exec conkeror -new chrome://"),
         ("M4-S-e", spawn "exec emacsclient -nc"),
         ("M4-S--", sendMessage Shrink),
         ("M4-S-=", sendMessage Expand),
         ("M4-S-t", withFocused $ windows . W.sink),
         ("M4-<Esc>", spawn "xmonad --recompile && xmonad --restart"),
         ("<XF86MonBrightnessDown>", spawn "brightness down"),
         ("<XF86MonBrightnessUp>", spawn "brightness up"),
         ("<XF86LaunchA>", goToSelected myGSConfig),
         ("<XF86LaunchB>", spawnSelected myGSConfig
                            ["netcfgd home",
                             "netcfgd cs",
                             "netcfgd cs-wired",
                             "netcfgd byu", 
                             "killall workrave",
                             "workrave",
                             "disp m",
                             "disp d",
                             "disp dm",
                             "disp m2d",
                             "disp d2m",
                             "disp class-on",
                             "disp class-off",
                             "xbacklight = 10"]),
         ("<XF86KbdBrightnessDown>", spawn "kbd_brightness off"),
         ("<XF86KbdBrightnessUp>", spawn "kbd_brightness on"),
         ("<XF86AudioPrev>", spawn "mpc_status.sh prev"),
         ("<XF86AudioPlay>", spawn "mpc_status.sh toggle"),
         ("<XF86AudioNext>", spawn "mpc_status.sh next"),
         ("<XF86AudioMute>", spawn "volume mute"),
         ("<XF86AudioLowerVolume>", spawn "volume down"),
         ("<XF86AudioRaiseVolume>", spawn "volume up"),
         ("M4-<XF86AudioRaiseVolume>", spawn "xte 'mouseclick 2'"),
         ("<XF86PowerOff>", spawn "mpc pause ; xlock -delay 20000 -usefirst")
       ]
       `removeKeysP`
       [ "M4-r", "M4-n", "M4-w", "M4-p", "M4-q", "M4-t", "M4-l", "M4-h", "M4-S-q" ]
       `removeMouseBindings`
       -- (mod4Mask, button1),
       [ (mod4Mask, button2), (mod4Mask, button3)]
       -- This doesn't work for copy/paste
       `additionalMouseBindings`
       [((controlMask, button1), (\_ -> spawn "xte 'mouseup 1' 'mouseclick 3'"))
       -- ,((mod4Mask, button1), (\_ -> spawn "xte 'mouseup 1' 'mouseclick 2'"))
       ]
                                          
