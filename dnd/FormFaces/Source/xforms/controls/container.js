// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Base class for all controls.
//
// Parameters:
//     element:       The element from which the control was created.
//     bind:          The control's bind, or null if it is unbound.
//     label:         The control's label, or null if it has none.
//     innerControls: The controls inside of this control.
//     isGroup:       Is the control a container for other controls?
function XFormContainerControl(element, bind, label, innerControls) {
  if (arguments.length == 0) {
    return;
  }

  assert(innerControls != null, "innerControls is null");
  
  XFormControl.call(this, element, bind, label);

  this.innerControls = innerControls;
  
  for (var i in this.innerControls) {
    assert(this.innerControls[i].enclosedBy == null, "enclosedBy is not null");
           this.innerControls[i].enclosedBy = this;
  }
};

XFormContainerControl.inherits(XFormControl);


// Parameters:
//     control: The control that was rendered.
//     binding: The XFormBinding to which the rendered control is bound, or null
//              if the control is unbound.
function XFormContainerControlInstance(control, binding, htmlNode, outerBinding, position) {
  if (arguments.length == 0) {
    return;
  }
  
  XFormControlInstance.call(this, control, binding, htmlNode, outerBinding, position);
  
  this.innerControlInstances = [];
};

XFormContainerControlInstance.inherits(XFormControlInstance);

XFormContainerControlInstance.prototype.activate = function() {
  for (var i in this.innerControlInstances)
  for (var j in this.innerControlInstances[i]) {
    this.innerControlInstances[i][j].activate();
  }
};

XFormContainerControlInstance.prototype.deactivate = function() {
  for (var i in this.innerControlInstances)
  for (var j in this.innerControlInstances[i]) {
    this.innerControlInstances[i][j].deactivate();
  }
};