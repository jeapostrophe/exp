// Copyright (c) 2000-2005 Progeny Systems Corporation.
//
// Consult license.html in the documentation directory for licensing
// information.


// An XPath token type.
// 
// See section 3.7 of the XPath specification for explanation of each of these
//  token types.
function XPathTokenType(name) {
  this.name = name;
};

XPathTokenType.prototype.toString = function() {
  return this.name;
};

XPathTokenType.LEFT_PARENTHESIS         = new XPathTokenType("LEFT_PARENTHESIS");
XPathTokenType.RIGHT_PARENTHESIS        = new XPathTokenType("RIGHT_PARENTHESIS");
XPathTokenType.LEFT_BRACKET             = new XPathTokenType("LEFT_BRACKET");
XPathTokenType.RIGHT_BRACKET            = new XPathTokenType("RIGHT_BRACKET");
XPathTokenType.DOT                      = new XPathTokenType("DOT");
XPathTokenType.DOT_DOT                  = new XPathTokenType("DOT_DOT");
XPathTokenType.ATTRIBUTE_SIGN           = new XPathTokenType("ATTRIBUTE_SIGN");
XPathTokenType.COMMA                    = new XPathTokenType("COMMA");
XPathTokenType.COLON_COLON              = new XPathTokenType("COLON_COLON");
                                                                                      
XPathTokenType.STAR                     = new XPathTokenType("STAR");
XPathTokenType.NAMESPACE_TEST           = new XPathTokenType("NAMESPACE_TEST");
XPathTokenType.QNAME                    = new XPathTokenType("QNAME");
                                                                                      
XPathTokenType.COMMENT                  = new XPathTokenType("COMMENT");
XPathTokenType.TEXT                     = new XPathTokenType("TEXT");
XPathTokenType.PROCESSING_INSTRUCTION   = new XPathTokenType("PROCESSING_INSTRUCTION");
XPathTokenType.NODE                     = new XPathTokenType("NODE");
                                                                                      
XPathTokenType.AND                      = new XPathTokenType("AND");
XPathTokenType.OR                       = new XPathTokenType("OR");
XPathTokenType.MOD                      = new XPathTokenType("MOD");
XPathTokenType.DIV                      = new XPathTokenType("DIV");
XPathTokenType.MULTIPLY                 = new XPathTokenType("MULTIPLY");
XPathTokenType.SLASH                    = new XPathTokenType("SLASH");
XPathTokenType.SLASH_SLASH              = new XPathTokenType("SLASH_SLASH");
XPathTokenType.UNION                    = new XPathTokenType("UNION");
XPathTokenType.PLUS                     = new XPathTokenType("PLUS");
XPathTokenType.MINUS                    = new XPathTokenType("MINUS");
XPathTokenType.EQUALS                   = new XPathTokenType("EQUALS");
XPathTokenType.NOT_EQUALS               = new XPathTokenType("NOT_EQUALS");
XPathTokenType.LESS_THAN                = new XPathTokenType("LESS_THAN");
XPathTokenType.LESS_THAN_OR_EQUAL_TO    = new XPathTokenType("LESS_THAN_OR_EQUAL_TO");
XPathTokenType.GREATER_THAN             = new XPathTokenType("GREATER_THAN");
XPathTokenType.GREATER_THAN_OR_EQUAL_TO = new XPathTokenType("GREATER_THAN_OR_EQUAL_TO");
                                                                                      
XPathTokenType.FUNCTION_NAME            = new XPathTokenType("FUNCTION_NAME");
                                                                                      
XPathTokenType.ANCESTOR                 = new XPathTokenType("ANCESTOR");
XPathTokenType.ANCESTOR_OR_SELF         = new XPathTokenType("ANCESTOR_OR_SELF");
XPathTokenType.ATTRIBUTE                = new XPathTokenType("ATTRIBUTE");
XPathTokenType.CHILD                    = new XPathTokenType("CHILD");
XPathTokenType.DESCENDANT               = new XPathTokenType("DESCENDANT");
XPathTokenType.DESCENDANT_OR_SELF       = new XPathTokenType("DESCENDANT_OR_SELF");
XPathTokenType.FOLLOWING                = new XPathTokenType("FOLLOWING");
XPathTokenType.FOLLOWING_SIBLING        = new XPathTokenType("FOLLOWING_SIBLING");
XPathTokenType.NAMESPACE                = new XPathTokenType("NAMESPACE");
XPathTokenType.PARENT                   = new XPathTokenType("PARENT");
XPathTokenType.PRECEDING                = new XPathTokenType("PRECEDING");
XPathTokenType.PRECEDING_SIBLING        = new XPathTokenType("PRECEDING_SIBLING");
XPathTokenType.SELF                     = new XPathTokenType("SELF");
                                                                                      
XPathTokenType.LITERAL                  = new XPathTokenType("LITERAL");
XPathTokenType.NUMBER                   = new XPathTokenType("NUMBER");
XPathTokenType.VARIABLE_REFERENCE       = new XPathTokenType("VARIABLE_REFERENCE");
                                                                                      
// Virtual token returned by the tokenizer at the end of every XPath expression.
XPathTokenType.END                      = new XPathTokenType("END");


// See the NodeType production in section 3.7 of the XPath specification.
XPathTokenType.prototype               .isNodeType = false;
XPathTokenType.COMMENT                 .isNodeType = true;
XPathTokenType.TEXT                    .isNodeType = true;
XPathTokenType.PROCESSING_INSTRUCTION  .isNodeType = true;
XPathTokenType.NODE                    .isNodeType = true;

// See the Operator production in section 3.7 of the XPath specification.
XPathTokenType.prototype               .isOperator = false;
XPathTokenType.AND                     .isOperator = true;
XPathTokenType.OR                      .isOperator = true;
XPathTokenType.MOD                     .isOperator = true;
XPathTokenType.DIV                     .isOperator = true;
XPathTokenType.MULTIPLY                .isOperator = true;
XPathTokenType.SLASH                   .isOperator = true;
XPathTokenType.SLASH_SLASH             .isOperator = true;
XPathTokenType.UNION                   .isOperator = true;
XPathTokenType.PLUS                    .isOperator = true;
XPathTokenType.MINUS                   .isOperator = true;
XPathTokenType.EQUALS                  .isOperator = true;
XPathTokenType.NOT_EQUALS              .isOperator = true;
XPathTokenType.LESS_THAN               .isOperator = true;
XPathTokenType.LESS_THAN_OR_EQUAL_TO   .isOperator = true;
XPathTokenType.GREATER_THAN            .isOperator = true;
XPathTokenType.GREATER_THAN_OR_EQUAL_TO.isOperator = true;

// See the AxisName production in section 3.7 of the XPath specification.
XPathTokenType.prototype               .isAxisName = false;
XPathTokenType.ANCESTOR                .isAxisName = true;
XPathTokenType.ANCESTOR_OR_SELF        .isAxisName = true;
XPathTokenType.ATTRIBUTE               .isAxisName = true;
XPathTokenType.CHILD                   .isAxisName = true;
XPathTokenType.DESCENDANT              .isAxisName = true;
XPathTokenType.DESCENDANT_OR_SELF      .isAxisName = true;
XPathTokenType.FOLLOWING               .isAxisName = true;
XPathTokenType.FOLLOWING_SIBLING       .isAxisName = true;
XPathTokenType.NAMESPACE               .isAxisName = true;
XPathTokenType.PARENT                  .isAxisName = true;
XPathTokenType.PRECEDING               .isAxisName = true;
XPathTokenType.PRECEDING_SIBLING       .isAxisName = true;
XPathTokenType.SELF                    .isAxisName = true;

// Checks that a lexeme is valid for a particular token type.
//
// Parameters:
//     type:   A token type.
//     lexeme: A lexeme to check.
//
// Return value:
//     True if lexeme is valid, false if not.
XPathTokenType.prototype.isValidLexeme = function(lexeme) {
  return lexeme.match(new RegExp("^(?:" + XPathTokenizer.regexFor(this) + ")$")) != null;
};


// Creates a new XPath token that has been read from an XPath expression string.
// 
// Parameters:
//     type:     The token's type.
//     lexeme:   The token's lexeme.
//     xpath:    The XPath expression string from which the token was read
//               (optional).
//     position: The position of the token within the XPath string (optional).
function XPathToken(type, lexeme, xpath, position) {
  if (arguments.length == 2) {
    xpath    = lexeme;
    position = 0;
  }
  
  this.type     = type;
  this.lexeme   = lexeme;
  this.xpath    = xpath;
  this.position = position;
};

XPathToken.prototype.toString = function() {
  return this.lexeme + " [" + this.type + "]";
};