// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new message action.
//
// Parameters:
//     element: The element from which this action was created.
//     level:   The message level identifier, one of "ephemeral", "modeless", or
//              "modal".
//     text:    The text of the message.
function XFormMessageAction(element, level, text) {
  assert(level == "ephemeral" || level == "modeless" || level == "modal", "bad level: " + level);
  assert(text  != null, "text is null");
  
  XFormAction.call(this, element);

  this.level = level;
  this.text  = text.toString().replace(/^\s+|\s+$/, "");
};

XFormMessageAction.inherits(XFormAction);


XFormParser.prototype.parseMessageAction = function(element) {
  return new XFormMessageAction(
    element,
    
    this.parseMessageActionLevel(element),
    this.parseMessageActionText (element)
  );
};

XFormParser.prototype.parseMessageActionLevel = function(element) {
  return this.stringValue(element, "level");
};

XFormParser.prototype.parseMessageActionText = function(element) {
  return XPathFunction.stringValueOf(element);
};


XFormMessageAction.prototype.activate = function() {
  switch (this.level) {
    case "modal":
      alert(this.text);
  }
};

XFormMessageAction.prototype.toString = function() {
  return "message";
};