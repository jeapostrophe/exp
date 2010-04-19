// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new toggle action.
//
// Parameters:
//     element:    The element from which this action was created.
//     switchCase: The case to switch to.
function XFormToggleAction(element, switchCase) {
  XFormAction.call(this, element);

  this.switchCase = switchCase;
};

XFormToggleAction.inherits(XFormAction);


XFormParser.prototype.parseToggleAction = function(element) {
  return new XFormToggleAction(
    element,
    this.parseToggleActionCase(element)
  );
};

XFormParser.prototype.parseToggleActionCase = function(element) {
  var switchCase = xform.getObjectById(element.attributes.getNamedItem("case"));
  
  if (!instanceOf(switchCase, XFormCaseControl)) {
    throw new XFormException(element, '"' + element.getAttribute("case") + '" is not the ID of a <case/> element.');
  }
  
  return switchCase;
};


XFormToggleAction.prototype.activate = function() {
  this.switchCase.toggle();
};

XFormToggleAction.prototype.toString = function() {
  return "toggle";
};