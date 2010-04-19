// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


var userAgent = { };

userAgent.isOpera            = (navigator.userAgent.match(/\bOpera\b/));
userAgent.isInternetExplorer = (navigator.userAgent.match(/\bMSIE\b/) && !userAgent.isOpera);
userAgent.isMozilla          = (navigator.userAgent.match(/\bGecko\b/));
userAgent.isKHTML            = (navigator.userAgent.match(/\b(Konqueror|KHTML)\b/));