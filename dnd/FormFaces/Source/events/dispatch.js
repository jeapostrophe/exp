// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


XmlEvent.builtinEvents = { };

// Registers a built-in event, defining if it bubbles, is cancelable, and what
// its default action is. When an event is defined, the pre-defined values
// override any values passed to dispatch().
//
// Parameters:
//     name:          The name of the event.
//     type:          The type of event (parameter to document.createEvent).
//     bubbles:       Does the event bubble?
//     cancelable:    Can the event be canceled?
//     defaultAction: An optional function to execute if the event is not
//                    canceled.
XmlEvent.define = function(name, type, bubbles, cancelable, defaultAction) {
  assert(!XmlEvent.builtinEvents[name], "event already defined");
  
  XmlEvent.builtinEvents[name] = {
    type:          type,
    bubbles:       bubbles,
    cancelable:    cancelable,
    defaultAction: defaultAction
  };
};

// Dispatches an event to the specified target element. If the event has been
// predefined, the type, bubbles, cancelable, and defaultAction parameters are
// ignored in favor of the predefined values.
//
// Parameters:
//     target:        The target element.
//     name:          The name of the event.
//     type:          The type of event (parameter to document.createEvent).
//     bubbles:       Does the event bubble?
//     cancelable:    Can the event be canceled?
//     defaultAction: An optional function to execute if the event is not
//                    canceled. The target of the event is passed as the first
//                    parameter when called.
XmlEvent.dispatch = function(target, name, type, bubbles, cancelable, defaultAction) {
  assert(target != null, "target is null");
  assert(name   != null, "name is null");
  
  if (XmlEvent.builtinEvents[name]) {
    var event = XmlEvent.builtinEvents[name];
    
    type          = event.type;
    bubbles       = event.bubbles;
    cancelable    = event.cancelable;
    defaultAction = event.defaultAction;
  }
  
  assert(type != null, "type is null");
  
  if (!defaultAction) {
    defaultAction = function() { };
  }
  
  status("Dispatching event " + name + " on " + xmlSerialize(target.cloneNode(false)));
    
  // W3C
  if (target.dispatchEvent) {
    if (name.match(/^DOM/)) {
      name = "_" + name;
    }
    
    var event = document.createEvent(type);
    
    event.initEvent(name, bubbles, cancelable);
    
    if (target.dispatchEvent(event) || !cancelable) {
      defaultAction(event);
    }
  }
  // Internet Explorer
  else {
    var fauxName = (XmlEvent.isBuiltinEvent(name)) ? name : "errorupdate";
    
    // Capture phase.
    var ancestors = [];
    
    for (var ancestor = target.parentNode; ancestor != null; ancestor = ancestor.parentNode) {
      ancestors.unshift(ancestor);
    }
    
    var len = ancestors.length;
    for (var i = 0; i < len; i++) {
      var event          = document.createEventObject();
          event.trueName = name;
          event.phase    = "capture";
          
      ancestors[i].fireEvent("on" + fauxName, event);
      
      if (event.stopped) {
        return;
      }
    }
    
    // Bubble phase.
    if (!bubbles) {
      // If the event doesn't bubble, add a handler that cancels bubbling since events
      // always bubble in Internet Explorer.
      var bubbleCanceler = new EventListener(target, name, "default", function(event) {
        event.cancelBubble = true;
      });
      
      bubbleCanceler.attach();
    }
    
    var event          = document.createEventObject();
        event.trueName = name;
        event.phase    = "default";
        event.target   = target;
        
    if (target.fireEvent("on" + fauxName, event) || !cancelable) {
      defaultAction(event);
    }
    
    if (!bubbles) {
      bubbleCanceler.detach();
    }
  }
};

XmlEvent.isBuiltinEvent = function(name) {
  switch (name) {
    case "abort":
    case "activate":
    case "afterprint":
    case "afterupdate":
    case "beforeactivate":
    case "beforecopy":
    case "beforecut":
    case "beforedeactivate":
    case "beforeeditfocus":
    case "beforepaste":
    case "beforeprint":
    case "beforeunload":
    case "beforeupdate":
    case "blur":
    case "bounce":
    case "cellchange":
    case "change":
    case "click":
    case "contextmenu":
    case "controlselect":
    case "copy":
    case "cut":
    case "dataavailable":
    case "datasetchanged":
    case "datasetcomplete":
    case "dblclick":
    case "deactivate":
    case "drag":
    case "dragend":
    case "dragenter":
    case "dragleave":
    case "dragover":
    case "dragstart":
    case "drop":
    case "error":
    case "errorupdate":
    case "filterchange":
    case "finish":
    case "focus":
    case "focusin":
    case "focusout":
    case "help":
    case "keydown":
    case "keypress":
    case "keyup":
    case "layoutcomplete":
    case "load":
    case "losecapture":
    case "mousedown":
    case "mouseenter":
    case "mouseleave":
    case "mousemove":
    case "mouseout":
    case "mouseover":
    case "mouseup":
    case "mousewheel":
    case "move":
    case "moveend":
    case "movestart":
    case "paste":
    case "propertychange":
    case "readystatechange":
    case "reset":
    case "resize":
    case "resizeend":
    case "resizestart":
    case "rowenter":
    case "rowexit":
    case "rowsdelete":
    case "rowsinserted":
    case "scroll":
    case "select":
    case "selectionchange":
    case "selectstart":
    case "start":
    case "stop":
    case "submit":
    case "unload":
      return true;
      
    default:
      return false;
  }
};