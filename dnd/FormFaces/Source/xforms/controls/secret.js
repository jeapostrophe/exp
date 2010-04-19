// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new secret control.
//
// Parameters:
//     element: The element from which the secret control was created.
//     bind:    The control's bind.
//     label:   The control's label.
function XFormSecretControl(element, bind, innerControls, incremental) {
  assert(bind  != null, "secret: bind is null");
  assert(innerControls != null, "innerControls is null");
  
  var labelControl = null;
  var len = innerControls.length;
  for (var i = 0; i < len; i++) {
    if (innerControls[i] != null && innerControls[i] == "label") {
      labelControl = innerControls[i];
    }
  }
  
  assert(labelControl != null, "secret: label is null");
  
  XFormControl.call(this, element, bind, innerControls);
  
  this.incremental = incremental;
};

XFormSecretControl.inherits(XFormControl);


XFormParser.prototype.parseSecretControl = function(element) {
  return new XFormSecretControl(
    element,
    
    this.getBindFor      (element),
    this.parseControls   (element),
    this.parseIncremental(element, false)
  );
};


XFormSecretControl.prototype.createInstance = function(binding, htmlNode, outerBinding) {
  return new XFormSecretControlInstance(this, binding, htmlNode, outerBinding);
};

function XFormSecretControlInstance(control, binding, htmlNode, outerBinding) {
  assert(binding != null, "binding is null");
  
  XFormControlInstance.call(this, control, binding, htmlNode, outerBinding);
  
  this.secret      = document.createElement("input");
  this.secret.type = "password";
  
  this.valueChangedOn(this.secret,
    this.control.incremental
      ? ["keypress", "keydown", "click", "mousedown", "change"]
      : ["change"]
  );
  
  this.watchForFocusChange(this.secret);
  this.activateOnEnter    (this.secret);
  
  // Fire "DOMActivate" events when the user presses enter.
  var self = this;
  
  new EventListener(this.secret, "keypress", null,
    function(event) {
      if (event.keyCode == 13) {
        XmlEvent.dispatch(self.htmlNode, "DOMActivate");
      }
    }
  );
};

XFormSecretControlInstance.inherits(XFormControlInstance);

XFormSecretControlInstance.prototype.addInstantiatedLabel = function(label) {
	this.control.label = label;
	this.htmlNode.appendChild(this.addLabel(this.secret));
};

XFormSecretControlInstance.prototype.getValue = function() {
  return this.secret.value;
};

XFormSecretControlInstance.prototype.setValue = function(value) {
  if (this.secret.value != value) {
      this.secret.value  = value;
  }
};

XFormSecretControlInstance.prototype.setReadOnly = function(isReadOnly) {
  this.secret.readOnly = isReadOnly;
};


XFormSecretControl        .prototype.toString =
XFormSecretControlInstance.prototype.toString = function() {
  return "secret";
};