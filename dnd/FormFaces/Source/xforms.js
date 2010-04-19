// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Load a number of other script files.
(function(scripts) {
  // Check for any other client XForms processors. If there is one, don't load
  // FormFaces. This code was written by Orion Ifland of Trinity Western
  // University.
  
  // Check for the xforms.xpi plugin on a Mozilla browser.
  if (document.implementation && document.implementation.hasFeature &&
      document.implementation.hasFeature("org.w3c.xforms.dom", "1.0")) {
    return;
  }
  // Check for the Novell ActiveX control in Internet Explorer.
  else if (navigator.userAgent.indexOf("nxforms") != -1) {
    // Novell does not remove itself from the user-agent string when you uninstall
    // the plug-in, so this check is unreliable.
    
    // return;
  }
  
  // Find the <script src="xforms.js"/> element that loaded this .js file so we
  // can figure out the path these scripts are stored in. For example, if this
  // script was referenced as <script src="/scripts/xforms.js"/> then we'll
  // prepend /scripts/ to each file name.
  var scriptElements = document.getElementsByTagName("script");
  var scriptPath     = null;
  var scriptEls      = scriptElements.length;
  
  for (var i = 0; i < scriptEls; ++i) {
    var scriptElement = scriptElements.item(i);
    var source        = scriptElement.getAttribute("src");
    
    if (source != null && source.match(/^(.*\/)?xforms\.js$/)) {
      scriptPath = RegExp.$1;
      break;
    }
  }
  
  // Load each of the scripts listed at the bottom of this file by dynamically
  // creating <script src="..."/> elements.
  var headElement = document.getElementsByTagName("head")[0];
  var scriptLen   = scripts.length;
  
  for (var i = 0; i < scriptLen; i++) {
    var newScriptElement = document.createElement("script");
    
    newScriptElement.setAttribute("type", "text/javascript");
    newScriptElement.setAttribute("src",  scriptPath + scripts[i]);
    
    headElement.insertBefore(newScriptElement, scriptElement.nextSibling);
  }
})

([
  "js/userAgent.js",
  "js/inheritance.js",
  "js/stackTrace.js",
  "js/assert.js",
  "js/monitor.js",
  "js/methodCall.js",
  "js/uniqueId.js",
  
  "xml/exception.js",
  "xml/loadDocument.js",
  "xml/importNode.js",
  "xml/namespaces.js",
  "xml/serialize.js",
  "xml/regexes.js",
  "xml/qualifiedName.js",
  
  "events/listener.js",
  "events/xmlEvent.js",
  "events/dispatch.js",
  
  "xpath/token.js",
  "xpath/tokenizer.js",
  "xpath/parser.js",
  "xpath/exception.js",
  
  "xpath/xpath.js",
  "xpath/qName.js",
  "xpath/nodeSet.js",
  "xpath/context.js",
  "xpath/axis.js",
  "xpath/nodeTest.js",
  "xpath/expression.js",
  "xpath/locationPath.js",
  "xpath/step.js",
  "xpath/predicate.js",
  "xpath/function.js",
  "xpath/functionResolver.js",
  "xpath/coreFunctions.js",
  
  "xforms/exception.js",
  "xforms/parser.js",
  "xforms/initialize.js",
  "xforms/xform.js",
  "xforms/object.js",
  "xforms/submission.js",
  "xforms/instance.js",
  "xforms/binding.js",
  "xforms/model.js",
  "xforms/dependencyGraph.js",
  
  "xforms/xpathFunctions.js",
  
  "xforms/controls/control.js",
  "xforms/controls/container.js",
  "xforms/controls/label.js",
  "xforms/controls/input.js",
  "xforms/controls/textArea.js",
  "xforms/controls/secret.js",
  "xforms/controls/output.js",
  "xforms/controls/select.js",
  "xforms/controls/trigger.js",
  "xforms/controls/group.js",
  "xforms/controls/repeat.js",
  "xforms/controls/switch.js",
  "xforms/controls/case.js",
  "xforms/controls/submit.js",

  "xforms/actions/action.js",
  "xforms/actions/series.js",
  "xforms/actions/load.js",
  "xforms/actions/message.js",
  "xforms/actions/setvalue.js",
  "xforms/actions/insert.js",
  "xforms/actions/delete.js",
  "xforms/actions/toggle.js",
  "xforms/actions/dispatch.js",
  "xforms/actions/rebuild.js",
  "xforms/actions/recalculate.js",
  "xforms/actions/revalidate.js",
  "xforms/actions/refresh.js",
  "xforms/actions/send.js",
  
  "xforms/loaded.js"
]);