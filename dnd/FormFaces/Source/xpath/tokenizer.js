// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// Creates a new XPath tokenizer, which takes an XPath string and breaks it up
// into the individual tokens needed during parsing.
//
// Parameters:
//     xpath: The string to tokenize.
function XPathTokenizer(xpath) {
  this.xpath        = xpath;
  this.position     = 0;
  this.currentToken = null;
  
  this.next();
};

// Scans the XPath string and reads the next token.
//
// Exceptions:
//     XPathInvalidCharacterException: Thrown if an invalid character was
//     encountered.
XPathTokenizer.prototype.next = function() {
  var nextToken = this.getToken();

  this.disambiguateToken(nextToken);
  this.currentToken = nextToken;
};

// Returns the next token from the XPath.
//
// Exceptions:
//     XPathInvalidCharacterException: Thrown if an invalid character was
//     encountered.
XPathTokenizer.prototype.getToken = function() {
  this.skipWhiteSpace();

  if (this.position == this.xpath.length) {
    return new XPathToken(XPathTokenType.END, "", this.xpath, this.xpath.length);
  }
  
  var regexeLen = XPathTokenizer.regexes.length;
  // Try each regular expression in order.
  for (var i = 0; i < regexeLen; ++i) {
    var entry     = XPathTokenizer.regexes[i];
    var tokenType = entry.tokenType;
    var regex     = entry.getTokenRegex;
    
    if (tokenType == XPathTokenType.END) {
      continue;
    }
    
    var match = regex.exec(this.xpath.substr(this.position));

    if (match != null) {
      this.position += match[0].length;

      return new XPathToken(tokenType, match[0], this.xpath, this.position - match[0].length);
    }
  }
  
  throw new XPathInvalidCharacterException(this.xpath, this.position);
};

// Determines the proper token type for an ambiguous lexeme based on the current
// context.
//
// Parameters:
//     nextToken: The token to disambiguate.
XPathTokenizer.prototype.disambiguateToken = function(nextToken) {
  var currentToken = this.currentToken;
  
  // Multiply operator '*' or named operators.
  if ((nextToken.type == XPathTokenType.STAR || nextToken.type == XPathTokenType.QNAME) && currentToken != null) {
    if (currentToken.type != XPathTokenType.ATTRIBUTE_SIGN   &&
        currentToken.type != XPathTokenType.COLON_COLON      &&
        currentToken.type != XPathTokenType.LEFT_PARENTHESIS &&
        currentToken.type != XPathTokenType.LEFT_BRACKET     &&
        currentToken.type != XPathTokenType.COMMA            &&
       !currentToken.type.isOperator)
    {
      switch (nextToken.lexeme) {
        case "*":   nextToken.type = XPathTokenType.MULTIPLY; break;
        case "and": nextToken.type = XPathTokenType.AND;      break;
        case "or":  nextToken.type = XPathTokenType.OR;       break;
        case "mod": nextToken.type = XPathTokenType.MOD;      break;
        case "div": nextToken.type = XPathTokenType.DIV;      break;
      }
    }
  }

  // Node types or function names.
  if (nextToken.type == XPathTokenType.QNAME && this.xpath.substr(this.position).match(/^\s*\(/)) {
    switch (nextToken.lexeme) {
      case "comment":                nextToken.type = XPathTokenType.COMMENT;                break;
      case "text":                   nextToken.type = XPathTokenType.TEXT;                   break;
      case "processing-instruction": nextToken.type = XPathTokenType.PROCESSING_INSTRUCTION; break;
      case "node":                   nextToken.type = XPathTokenType.NODE;                   break;
      default:                       nextToken.type = XPathTokenType.FUNCTION_NAME;          break;
    }
  }

  // Axis names.
  if (nextToken.type == XPathTokenType.QNAME && this.xpath.substr(this.position).match(/^\s*::/)) {
    switch (nextToken.lexeme) {
      case "ancestor":           nextToken.type = XPathTokenType.ANCESTOR;           break;
      case "ancestor-or-self":   nextToken.type = XPathTokenType.ANCESTOR_OR_SELF;   break;
      case "attribute":          nextToken.type = XPathTokenType.ATTRIBUTE;          break;
      case "child":              nextToken.type = XPathTokenType.CHILD;              break;
      case "descendant":         nextToken.type = XPathTokenType.DESCENDANT;         break;
      case "descendant-or-self": nextToken.type = XPathTokenType.DESCENDANT_OR_SELF; break;
      case "following":          nextToken.type = XPathTokenType.FOLLOWING;          break;
      case "following-sibling":  nextToken.type = XPathTokenType.FOLLOWING_SIBLING;  break;
      case "namespace":          nextToken.type = XPathTokenType.NAMESPACE;          break;
      case "parent":             nextToken.type = XPathTokenType.PARENT;             break;
      case "preceding":          nextToken.type = XPathTokenType.PRECEDING;          break;
      case "preceding-sibling":  nextToken.type = XPathTokenType.PRECEDING_SIBLING;  break;
      case "self":               nextToken.type = XPathTokenType.SELF;               break;
    }
  }
};


// Advances the current position to the next non-whitespace character, or to the
// end of the XPath if there is none.
XPathTokenizer.prototype.skipWhiteSpace = function() {
  while (this.position < this.xpath.length && this.xpath.substr(this.position, 1).match(/^\s$/)) {
    ++this.position;
  }
};


(function() {
  XPathTokenizer.regexes = [
    {tokenType: XPathTokenType.LEFT_PARENTHESIS,         regex: "\\("},
    {tokenType: XPathTokenType.RIGHT_PARENTHESIS,        regex: "\\)"},
    {tokenType: XPathTokenType.LEFT_BRACKET,             regex: "\\["},
    {tokenType: XPathTokenType.RIGHT_BRACKET,            regex: "\\]"},
    {tokenType: XPathTokenType.DOT_DOT,                  regex: "\\.\\."},
    {tokenType: XPathTokenType.DOT,                      regex: "\\."},
    {tokenType: XPathTokenType.ATTRIBUTE_SIGN,           regex: "@"},
    {tokenType: XPathTokenType.COMMA,                    regex: ","},
    {tokenType: XPathTokenType.COLON_COLON,              regex: "::"},

    {tokenType: XPathTokenType.STAR,                     regex: "\\*"},
    {tokenType: XPathTokenType.NAMESPACE_TEST,           regex: XmlRegexes.NCName + ":\\*"},
    {tokenType: XPathTokenType.QNAME,                    regex: XmlRegexes.QName},

    {tokenType: XPathTokenType.COMMENT,                  regex: "comment"},
    {tokenType: XPathTokenType.TEXT,                     regex: "text"},
    {tokenType: XPathTokenType.PROCESSING_INSTRUCTION,   regex: "processing-instruction"},
    {tokenType: XPathTokenType.NODE,                     regex: "node"},

    {tokenType: XPathTokenType.AND,                      regex: "and"},
    {tokenType: XPathTokenType.OR,                       regex: "or"},
    {tokenType: XPathTokenType.MOD,                      regex: "mod"},
    {tokenType: XPathTokenType.DIV,                      regex: "div"},
    {tokenType: XPathTokenType.SLASH_SLASH,              regex: "//"},
    {tokenType: XPathTokenType.SLASH,                    regex: "/"},
    {tokenType: XPathTokenType.UNION,                    regex: "\\|"},
    {tokenType: XPathTokenType.PLUS,                     regex: "\\+"},
    {tokenType: XPathTokenType.MINUS,                    regex: "-"},
    {tokenType: XPathTokenType.MULTIPLY,                 regex: "\\*"},
    {tokenType: XPathTokenType.EQUALS,                   regex: "="},
    {tokenType: XPathTokenType.NOT_EQUALS,               regex: "!="},
    {tokenType: XPathTokenType.LESS_THAN_OR_EQUAL_TO,    regex: "<="},
    {tokenType: XPathTokenType.LESS_THAN,                regex: "<"},
    {tokenType: XPathTokenType.GREATER_THAN_OR_EQUAL_TO, regex: ">="},
    {tokenType: XPathTokenType.GREATER_THAN,             regex: ">"},

    {tokenType: XPathTokenType.FUNCTION_NAME,            regex: XmlRegexes.QName},

    {tokenType: XPathTokenType.ANCESTOR,                 regex: "ancestor"},
    {tokenType: XPathTokenType.ANCESTOR_OR_SELF,         regex: "ancestor-or-self"},
    {tokenType: XPathTokenType.ATTRIBUTE,                regex: "attribute"},
    {tokenType: XPathTokenType.CHILD,                    regex: "child"},
    {tokenType: XPathTokenType.DESCENDANT,               regex: "descendant"},
    {tokenType: XPathTokenType.DESCENDANT_OR_SELF,       regex: "descendant-or-self"},
    {tokenType: XPathTokenType.FOLLOWING,                regex: "following"},
    {tokenType: XPathTokenType.FOLLOWING_SIBLING,        regex: "following-sibling"},
    {tokenType: XPathTokenType.NAMESPACE,                regex: "namespace"},
    {tokenType: XPathTokenType.PARENT,                   regex: "parent"},
    {tokenType: XPathTokenType.PRECEDING,                regex: "preceding"},
    {tokenType: XPathTokenType.PRECEDING_SIBLING,        regex: "preceding-sibling"},
    {tokenType: XPathTokenType.SELF,                     regex: "self"},

    {tokenType: XPathTokenType.LITERAL,                  regex: "(?:\"[^\"]*\"|'[^']*')"},
    {tokenType: XPathTokenType.NUMBER,                   regex: "(?:[0-9]+(?:\\.[0-9]*)?|\\.[0-9]+)"},
    {tokenType: XPathTokenType.VARIABLE_REFERENCE,       regex: "\\$" + XmlRegexes.QName},

    {tokenType: XPathTokenType.END,                      regex: ""}
  ];
  
  // Pre-compile all of the regular expressions used by the getToken method.
  for (var i = XPathTokenizer.regexes.length - 1; i >= 0; --i) {
    var entry = XPathTokenizer.regexes[i];
    entry.getTokenRegex = new RegExp("^(?:" + entry.regex + ")");
  }
}) ();

XPathTokenizer.regexFor = function(tokenType) {
  for (var i = XPathTokenizer.regexes.length - 1; i >= 0; --i) {
    var entry = XPathTokenizer.regexes[i];
    
    if (entry.tokenType == tokenType) {
      return entry.regex;
    }
  }
};