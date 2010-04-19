// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new trigger control.
//
// Parameters:
//     element:    The element from which the trigger control was created.
//     bind:       The control's bind.
//     label:      The control's label.
//     appearance: The appearance of the control.
function XFormTriggerControl(element, bind, innerControls, appearance) {
  if (arguments.length == 0) {
    return;
  }

  assert(innerControls != null, "innerControls is null");
  
  var labelControl     = null;
  var numInnerControls = innerControls.length;
  
  for (var i = 0; i < numInnerControls; i++) {
    if (innerControls[i] != null && innerControls[i] == "label") {
      labelControl = innerControls[i];
    }
  }
  
  assert(labelControl != null, "trigger: label is null");
  
  XFormControl.call(this, element, bind, innerControls, appearance);
};

XFormTriggerControl.inherits(XFormControl);


XFormParser.prototype.parseTriggerControl = function(element) {
  return new XFormTriggerControl(
    element,
    
    this.getBindFor     (element),
    this.parseControls  (element),
    this.parseAppearance(element, "full")
  );
};



XFormTriggerControl.prototype.createInstance = function(binding, htmlNode, outerBinding, position) {
  return new XFormTriggerControlInstance(this, binding, htmlNode, outerBinding, position);
};

function XFormTriggerControlInstance(control, binding, htmlNode, outerBinding, position) {
  if (arguments.length == 0) {
    return;
  }

  XFormControlInstance.call(this, control, binding, htmlNode, outerBinding, position);
  
  var self = this;
  
  switch (control.appearance) {
    case "full":
    case "compact":
      this.button       = document.createElement("input");
      this.button.type  = "button";
      this.button.value = "";
      
      this.htmlNode.appendChild(this.button);
      this.watchForFocusChange (this.button);
      
      // Fire "DOMActivate" events when the button is clicked.
      new EventListener(this.button, "click", null,
        functionCall(XmlEvent.dispatch, this.htmlNode, "DOMActivate"));
      
      break;
      
    case "minimal":
      this.anchor      = document.createElement("a");
      this.anchor.href = "javascript:void(0)";
      
      this.htmlNode.appendChild(this.anchor);
      this.watchForFocusChange (this.anchor);
      
      // Fire "DOMActivate" events when the link is clicked.
      new EventListener(this.anchor, "click", null,
        functionCall(XmlEvent.dispatch, this.htmlNode, "DOMActivate"));
      
      break;
      
    default:
      assert(false, "Unknown appearance value: " + this.appearance);
  }
};

XFormTriggerControlInstance.inherits(XFormControlInstance);

XFormTriggerControlInstance.prototype.addInstantiatedLabel = function(label) {
  this.label = label;
  var self   = this;
  
  switch (this.control.appearance) {
    case "full":
    case "compact":
      this.button.value = label.getValue();
      
      // When the label text changes, change the button's label.
      this.label.addListener("text", function(control, property, value) {
        self.button.value = value;
      });
      
      break;
      
    case "minimal":
      this.anchor.appendChild(document.createTextNode(label.getValue()));
      
      // When the label text changes, change the anchor's text.
      this.label.addListener("text", function(control, property, value) {
        self.anchor.replaceChild(document.createTextNode(value), self.anchor.firstChild);
      });
      
      break;
  }
};

XFormTriggerControl        .prototype.toString =
XFormTriggerControlInstance.prototype.toString = function() {
  return "trigger";
};