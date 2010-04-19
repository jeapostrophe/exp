// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new submit control.
//
// Parameters:
//     element:    The element from which the trigger control was created.
//     bind:       The control's bind.
//     label:      The control's label.
//     appearance: The control's appearance.
//     submission: The submission to trigger.
function XFormSubmitControl(element, bind, innerControls, appearance, submission) {
  assert(innerControls != null, "innerControls is null");
  XFormTriggerControl.call(this, element, bind, innerControls, appearance);
  
  this.submission = submission;
};

XFormSubmitControl.inherits(XFormTriggerControl);


XFormParser.prototype.parseSubmitControl = function(element) {
  return new XFormSubmitControl(
    element,
    
    this.getBindFor                  (element),
    this.parseControls               (element),
    this.parseAppearance             (element, "full"),
    this.parseSubmitControlSubmission(element)
  );
};

XFormParser.prototype.parseSubmitControlSubmission = function(element) {
  return xform.getObjectById(element.attributes.getNamedItem("submission"));
};


XFormSubmitControl.prototype.createInstance = function(binding, htmlNode, outerBinding, position) {
  return new XFormSubmitControlInstance(this, binding, htmlNode, outerBinding, position);
};

function XFormSubmitControlInstance(control, binding, htmlNode, outerBinding, position) {
  XFormTriggerControlInstance.call(this, control, binding, htmlNode, outerBinding, position);
  
  // When the control is activated fire xforms-submit on the submission.
  new EventListener(this.htmlNode, "DOMActivate", null,
    functionCall(XmlEvent.dispatch, this.control.submission.htmlNode, "xforms-submit"));
};

XFormSubmitControlInstance.inherits(XFormTriggerControlInstance);


XFormSubmitControl        .prototype.toString =
XFormSubmitControlInstance.prototype.toString = function() {
  return "submit";
};