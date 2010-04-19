// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new send action.
//
// Parameters:
//     element:    The element from which this action was created.
//     submission: The submission object to submit.
function XFormSendAction(element, submission) {
  assert(submission != null, "submission is null");
  
  XFormAction.call(this, element);

  this.submission = submission;
};

XFormSendAction.inherits(XFormAction);


XFormParser.prototype.parseSendAction = function(element) {
  return new XFormSendAction(
    element,
    
    this.parseSendActionSubmission(element)
  );
};

XFormParser.prototype.parseSendActionSubmission = function(element) {
  return xform.getObjectById(element.attributes.getNamedItem("submission"), XFormSubmission);
};


XFormSendAction.prototype.activate = function() {
  XmlEvent.dispatch(this.submission.htmlNode, "xforms-submit");
};

XFormSendAction.prototype.toString = function() {
  return "send";
};