// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new event listener and attaches it to the requested element.
//
// Parameters:
//     observer: The element to attach the listener to.
//     name:     The event name.
//     phase:    The phase to listen in. One of "capture", "default"/"bubble",
//               or null. If null then the listener is only triggered if the
//               event is fired directly on the observer.
//     handler:  A function to call when the event is fired.
function EventListener(observer, name, phase, handler) {
  assert(observer != null, "observer is null");
  assert(name     != null, "name is null");
  
  // Create a list of all the event listeners that have been created. Internet
  // Explorer does not seem to release these automatically when the page is
  // unloaded, so we'll need to detach them ourselves when the page is unloaded.
  if (typeof(EventListener.all) == "undefined") {
    EventListener.all = [];
    
    new EventListener(window, "unload", "default", function() {
      for (var i = EventListener.all.length - 1; i >= 0; --i) {
        EventListener.all[i].detach();
      }
    });
  }
  
  EventListener.all.push(this);

  // "bubble" is synonymous with "default".
  if (phase == "bubble") {
    phase = "default";
  }
  
  this.observer = observer;
  this.name     = name;
  this.phase    = phase;
  
  this.callback = function(event) {
    // Internet Explorer-specific event massaging.
    if (userAgent.isInternetExplorer) {
      if (event == null) {
        event = window.event;
      }
      
      event.target = event.srcElement; 
      
      // fireEvent does not accept user-defined event names, so all nonstandard events
      // become "onerrorupdate" events with trueName set to the real event name.
      if (typeof(event.trueName) != "undefined" && event.trueName != name) {
        return;
      }
      
      // If the event was triggered by the user calling fireEvent, check that the
      // expected phase is not "capture".
      if (typeof(event.phase) == "undefined") {
        if (phase == "capture") {
          return;
        }
      }
      // If the event was triggered by XFormEvent.dispatch, then make sure we're in
      // the expected phase.
      else if (event.phase != phase && phase != null) {
        return;
      }
      
      // Internet Explorer does not support the capture phase natively, so we simulate
      // it by firing the event manually on the target element's ancestor elements and
      // immediately cancelling the bubbling.
      if (phase == "capture") {
        event.cancelBubble = true;
      }
      
      event.preventDefault = function() {
        this.returnValue = false;
      };
      
      event.stopPropagation = function() {
        this.cancelBubble = true;
        this.stopped      = true;
      };
    }
    
    // Safari may set the target to be a text node; if so, use the text node's
    // parent.
    if (event.target != null && isTextNode(event.target)) {
      event.target = event.target.parentNode;
    }
    
    // If the phase is null, then the event must be fired directly on the observer.
    if (phase == null && event.target != observer) {
      return;
    }
    
    // Function to call the handler and then clean up.
    var callHandler = function(event) {
      handler.call(event.target, event);
      
      // Need to get rid of the functions that were created above to prevent Internet
      // Explorer from leaking memory due to circular references from the function
      // closures.
      if (userAgent.isInternetExplorer) {
        event.preventDefault  = null;
        event.stopPropagation = null;
      }
    };

    // Call the handler in 1ms to give time for the UI to be redrawn, unless we're
    // unloading the page in which case we need to call it immediately.
    if (name == "unload") {
      monitor(functionCall(callHandler, event));
    }
    else {
      // Make a copy of the event object. It will get reset by the time the event
      // handler is called.
      var eventClone = {};
      
      for (var i = event.length - 1; i >= 0; --i) {
        eventClone[i] = event[i];
      }
      
      setTimeout(functionCall(monitor, functionCall(callHandler, eventClone)), 1);
    }
  };
  
  this.attach();
};

// W3C methods.
if (document.addEventListener) {
  EventListener.prototype.attach = function() {
    // Opera does not have window.addEventListener, and instead fires events from
    // the document node.
    if (this.observer == window && !window.addEventListener) {
      this.observer = document;
    }
    
    if (this.observer.addEventListener) {
      var name = this.name;
      
      if (name.match(/^DOM/)) {
        name = "_" + name;
      }
      
      this.observer.addEventListener(name, this.callback, this.phase == "capture");
    }
  };
  
  EventListener.prototype.detach = function() {
    // Opera does not have window.removeEventListener, and instead fires events from
    // the document node.
    if (this.observer == window && !window.removeEventListener) {
      this.observer = document;
    }
    
    if (this.observer.removeEventListener) {
      var name = this.name;
      
      if (name.match(/^DOM/)) {
        name = "_" + name;
      }
      
      this.observer.removeEventListener(name, this.callback, this.phase == "capture");
    }
  };
}
// Internet Explorer methods.
else {
  EventListener.prototype.attach = function() {
    if (this.observer.attachEvent) {
      this.observer.attachEvent(this.getName(), this.callback);
    }
  };
  
  EventListener.prototype.detach = function() {
    if (this.observer.detachEvent) {
      this.observer.detachEvent(this.getName(), this.callback);
    }
  };
  
  EventListener.prototype.getName = function() {
    if (this.phase == "capture" || !XmlEvent.isBuiltinEvent(this.name)) {
      return "onerrorupdate";
    }
    
    return "on" + this.name;
  };
}