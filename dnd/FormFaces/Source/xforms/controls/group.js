// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new XForms group control.
//
// Parameters:
//     element:       The element from which the group control was created.
//     bind:          The control's bind.
//     label:         The control's label, or null if it has none.
//     innerControls: The controls immediately enclosed by the group.
function XFormGroupControl(element, bind, innerControls) {
  assert(innerControls != null, "innerControls is null");
  
  XFormControl.call(this, element, bind, innerControls);
};

XFormGroupControl.inherits(XFormControl);


XFormParser.prototype.parseGroupControl = function(element) {
  var bind          = this.getBindFor   (element);
  var innerControls = this.parseControls(element);
  
  return new XFormGroupControl(element, bind, innerControls);
};


XFormGroupControl.prototype.createInstance = function(binding, htmlNode, outerBinding) {
  return new XFormGroupControlInstance(this, binding, htmlNode, outerBinding);
};

function XFormGroupControlInstance(control, binding, htmlNode, outerBinding) {
  XFormControlInstance.call(this, control, binding, htmlNode, outerBinding);
  
  this.container = document.createElement("span");
  
  var labelElement = this.getLabelElement();
  
  if (labelElement == null) {
    this.htmlNode.appendChild(this.addLabel(this.container));
  }
};

XFormGroupControlInstance.inherits(XFormControlInstance);

XFormGroupControlInstance.prototype.addInstantiatedLabel = function(label) {
  this.control.label = label;
  this.htmlNode.appendChild(this.addLabel(this.container));
};

XFormGroupControl        .prototype.toString =
XFormGroupControlInstance.prototype.toString = function() {
  return "group";
};