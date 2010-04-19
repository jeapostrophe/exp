// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


XmlSchemaTypes.DECIMAL = new XmlSchemaType()
  .assignName     (new QualifiedName(XmlNamespaces.SCHEMA, "decimal"))
  .facetWhiteSpace("collapse");

XmlSchemaTypes.DECIMAL.errorMessageFor = function(value) {
  if (this.canonicalValue(value) == null) {
    return "%q is not a valid number.";
  }

  var wholeDigits    = RegExp.$2; // From call to canonicalValue.
  var fractionDigits = RegExp.$4;

  if (this.totalDigits != null) {
    if (wholeDigits.length + fractionDigits.length > this.totalDigits) {
      return "%q has too many digits.";
    }
  }

  if (this.fractionDigits != null) {
    if (fractionDigits.length > this.fractionDigits) {
      return "%q has too many digits after the decimal point.";
    }
  }

  if (this.maxInclusive != null) {
    if (value > this.maxInclusive) {
      return "%q is too large.";
    }
  }

  if (this.maxExclusive != null) {
    if (value >= this.maxExclusive) {
      return "%q is too large.";
    }
  }

  if (this.minInclusive != null) {
    if (value < this.minInclusive) {
      return "%q is too small.";
    }
  }

  if (this.minExclusive != null) {
    if (value <= this.minExclusive) {
      return "%q is too small.";
    }
  }

  return this.baseType.errorMessageFor.call(this, value);
};

XmlSchemaTypes.DECIMAL.canonicalValue = function(value) {
  value = this.baseType.canonicalValue.call(this, value);

  // The value must contain at least one digit. We must test for this separately
  // since the following regular expression would otherwise allow both the whole
  // and fractional portions of the number to be omitted.
  if (!value.match(/\d/)) {
    return null;
  }

  if (value.match(/^([-+]?)0*(\d*)(?:(\.(\d+?))0*)?$/)) {
    return RegExp.$1 + RegExp.$2 + RegExp.$3;
  }
  else {
    return null;
  }
};