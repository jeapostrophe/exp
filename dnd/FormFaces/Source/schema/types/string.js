// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


XmlSchemaTypes.STRING = new XmlSchemaType()
  .assignName     (new QualifiedName(XmlNamespaces.SCHEMA, "string"))
  .facetWhiteSpace("preserve");

XmlSchemaTypes.STRING.errorMessageFor = function(value) {
  value = this.canonicalValue(value);
  
  if (value.match(/([^\t\r\n\u0020-\uD7FF\uE000-\uFFFD\u10000-\u10FFFF])/)) {
    return '%q contains an invalid character: ' + RegExp.$1 + " (" + (+RegExp.$1) + ").";
  }

  if (this.length != null) {
    if (value.length < this.length) {
      return "%q is too short.";
    }

    if (value.length > this.length) {
      return "%q is too long.";
    }
  }

  if (this.minLength != null) {
    if (value.length < this.minLength) {
      return "%q is too short.";
    }
  }

  if (this.maxLength != null) {
    if (value.length > this.maxLength) {
      return "%q is too long.";
    }
  }

  return this.baseType.errorMessageFor.call(this, value);
};