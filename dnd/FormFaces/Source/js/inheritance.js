// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


Function.prototype.inherits  = function(BaseClass) {
  this.prototype             = new BaseClass;
  this.prototype.constructor = this;
  this.base                  = BaseClass;
};

function instanceOf(object, Class) {
  if (object == null) {
    return false;
  }
  
  for (var constructor = object.constructor; constructor != null; constructor = constructor.base) {
    if (constructor == Class) {
      return true;
    }
  }
  
  return false;
};