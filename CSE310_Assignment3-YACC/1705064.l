%option noyywrap yylineno

%{
#include<iostream>
#include<fstream>
#include<string>
#include "Symbol_table.cpp"
#include "y.tab.h"

using namespace std;

extern SymbolTable* st;
//YYSTYPE yylval;
extern ofstream logfile,errorfile;
int error_count=0;
int line_count=1;
int str_len;
char ch;
string str;

void inc_ec(){
	error_count++;
}

int lineno(){return line_count;}

char change_char(string str){	
	char res;
	if(str[1] != '\\'){
		res = str[1];				
	}
	else if(str[1] == '\\' && (str[2] == 'n' || str[2] == '0')){
		res = '\n';		
	}
	else if(str[1] == '\\' && str[2] == 't'){
		res = '\t';		
	}	
	else if(str[1] == '\\' && str[2] == 'r'){
		res = '\r';		
	}	
	else if(str[1] == '\\' && str[2] == 'b'){
		res = '\b';		
	}	
	else if(str[1] == '\\' && str[2] == 'v'){
		res = '\v';		
	}
	else if(str[1] == '\\' && str[2] == 'a'){
		res = '\a';		
	}
	else if(str[1] == '\\' && str[2] == 'f'){
		res = '\f';		
	}
	return res;
}

int line_inc(string str){
	int n=0;
	for(int i=0;i<str.size();i++)
		if(str[i] == '\n'){
			line_count++;
			n++;
		}							
	return n;
}

string merge_string(string s){
	string result = "";
	for(int i=0;i<s.size();i++){
		if(s[i] == '\\' && (s[i+1] == '\n' || s[i+1] == '0') || s[i] == '\n')
			result = result;
		else{
            if(s[i]=='\\' && (s[i+1]=='t')){
            	s[i] = '\t';
            	result += s[i];
            	i++;
            }
            else if(s[i]=='\\' && (s[i+1]=='n')){
            	s[i] = '\n';
            	result += s[i];
            	i++;
            }
            else if(s[i]=='\\' && (s[i+1]=='r')){
            	s[i] = '\r';            	
            	result += s[i];
            	i++;
            }
            else if(s[i]=='\\' && (s[i+1]=='b')){
            	s[i] = '\b';            	
            	result += s[i];
            	i++;
            }
            else if(s[i]=='\\' && (s[i+1]=='v')){
            	s[i] = '\v';            	
            	result += s[i];
            	i++;
            }
            else if(s[i]=='\\' && (s[i+1]=='v')){
            	s[i] = '\a';            	
            	result += s[i];
            	i++;
            }
            else if(s[i]=='\\' && (s[i+1]=='f')){
            	s[i] = '\f';            	
            	result += s[i];
            	i++;
            }
            else if(s[i] == '\\' && (s[i+1] == '"')){
            	s[i] = '"';
            	result += s[i];
            	i++;
            }
            
	        else result += s[i];
		}
	}	
	return result;
}

  	
%}

ws [ \t\v]+
newline [\n]
Digits [0-9] 
Letter [a-zA-Z]
any_char [+\-\*,\.;=\}\{\[\]?\"\/\\\']
Identifier ({Letter}|_)({Letter}|{Digits}|_)*
esc ((\\n)|(\\t)|(\\r)|(\\b)|(\\v)|(\\0)|(\\a)|(\\f)) 
Character_literals \'(({Letter}|{esc}|[+\-\*\{\}\[\];\.])|{Letter}{ws})\'
string_literals ((\"({Letter}|{ws}|{esc}|{any_char})+\")|((\")(({Letter}|{ws}|{esc}|{any_char})+(\\{newline}({Letter}|{ws}|{esc}|{any_char}))*)*\"))
Integer_literals {Digits}+
comments (((\/\*)(({ws}|{Letter}|{Digits}|{any_char}|{esc})*{newline}*({ws}|{Letter}|{Digits}|{any_char}|{esc})*)*(\*\/))|(\/\/({ws}|{Letter}|{Digits}|{any_char}|{esc})*((\\{newline})+)?(({ws}|{Letter}|{Digits}|{any_char}|{esc})*)?))
CONST_FLOAT {Digits}*(\.{Integer_literals})?([Ee][+-]?{Integer_literals})?

decimal_point_error {Integer_literals}((\.{Integer_literals})|\.)*
inv_char_error ((\'({Letter}|{esc}|[+\-\*,\.;\\\}\{\[\]])*)|(\'\\\'))
inv_str_error \"(({Letter}|{esc}|[+\-\*,\.;\\\}\{\[\]])(\\{newline}{Letter})*)*
inv_comm_error \/\*({Letter}|{ws}|[+\-\*,\.;\\\}\{\[\]]|{newline})*
ill_formed {Integer_literals}(((\.{Integer_literals})?[Ee][+-]?{Integer_literals}\.{Integer_literals})*|(\.([Ee][+-]?{Integer_literals})*))
invalid (({Digits}+{Identifier}+)|({Digits}+\.{Digits}*{Letter}+{Digits}*)|({Digits}+E[+-]?{Letter}+)|({Digits}*\.{Digits}+E[+-]{Letter}+))
multi_char_error \'{Letter}{Letter}+\'
emp_char_error \'{ws}*\'


%%
{ws} {}
(if) {yylval.svar = yytext; return IF;}
(for) {yylval.svar = yytext; return FOR;}
(do) {yylval.svar = yytext; return DO;}
(float) {yylval.svar = yytext; return FLOAT;}
(void) {yylval.svar = yytext; return VOID;}
(int) {yylval.svar = yytext; return INT;}
(else) {yylval.svar = yytext; return ELSE;}
(while) {yylval.svar = yytext; return WHILE;}
(char) {yylval.svar = yytext; return CHAR;}
(double) {yylval.svar = yytext; return DOUBLE;}
(return) {yylval.svar = yytext; return RETURN;}
(continue) {yylval.svar = yytext; return CONTINUE;}
(printf) {yylval.svar = yytext; return PRINTLN;}

"++" {
	SymbolInfo* si = new SymbolInfo(yytext,"INCOP");
	yylval.symval = si; 
	return INCOP;}
"--" {
	SymbolInfo* si = new SymbolInfo(yytext,"DECOP");
	yylval.symval = si; 
	return DECOP;}
[+-] {
	SymbolInfo* si = new SymbolInfo(yytext,"ADDOP");
	yylval.symval = si;
	return ADDOP;}
[*/%] {
	SymbolInfo* si = new SymbolInfo(yytext,"MULOP");
	yylval.symval = si;		 
	return MULOP;}
"<"|"<="|">"|">="|"=="|"!=" {
	SymbolInfo* si = new SymbolInfo(yytext,"RELOP");
	yylval.symval = si; 
	return RELOP;}
"!" {
	SymbolInfo* si = new SymbolInfo(yytext,"NOT");
	yylval.symval = si; 
	return NOT;}
"=" {
	SymbolInfo* si = new SymbolInfo(yytext,"ASSIGNOP");
	yylval.symval = si; 
	return ASSIGNOP;}
"&&"|"||" {
	SymbolInfo* si = new SymbolInfo(yytext,"LOGICOP");
	yylval.symval = si; 
	return LOGICOP;}
"(" {yylval.svar = yytext; return LPAREN;}
")" {yylval.svar = yytext; return RPAREN;}
"{" {yylval.svar = yytext; return LCURL;} 
"}" {yylval.svar = yytext; return RCURL;}
"[" {yylval.svar = yytext; return LTHIRD;}
"]" {yylval.svar = yytext; return RTHIRD;}
"," {yylval.svar = yytext; return COMMA;}
";" {yylval.svar = yytext; return SEMICOLON;}

{Identifier} {
	SymbolInfo* id = new SymbolInfo();
	id->set_name((string)yytext); id->set_type("ID"); yylval.symval = id; return ID;			
	}
{string_literals} {}
{Character_literals} {}
{Integer_literals}+ {
	SymbolInfo* si = new SymbolInfo(yytext,"CONST_INT");
	yylval.symval = si; 
	return CONST_INT;}
{CONST_FLOAT} {
	SymbolInfo* si = new SymbolInfo(yytext,"CONST_FLOAT");
	yylval.symval = si; 
	return CONST_FLOAT;}

{comments} {str_len = line_inc(yytext);}

{decimal_point_error} {inc_ec();errorfile<<"\nError at line no "<<lineno()<<": Too many decimal points "<<yytext<<endl;}
{ill_formed} {inc_ec();errorfile<<"\nError at line no "<<lineno()<<": Ill formed number "<<yytext<<endl;}
{invalid} {inc_ec();errorfile<<"\nError at line no "<<lineno()<<": Invalid prefix on ID or invalid suffix on Number "<<yytext<<endl;}
{multi_char_error} {inc_ec();errorfile<<"\nError at line no "<<lineno()<<": Multi character constant error "<<yytext<<endl;}
{emp_char_error} {inc_ec();errorfile<<"\nError at line no "<<lineno()<<": Empty character constant error "<<yytext<<endl;}
{inv_char_error} {inc_ec();errorfile<<"\nError at line no "<<lineno()<<": Unterminated character "<<yytext<<endl;} 
{inv_str_error} {str_len = line_inc(yytext);str = merge_string(yytext);inc_ec();errorfile<<"\nError at line no "<<lineno()-str_len<<": Unterminated String "<<yytext<<endl;}
{inv_comm_error} {str_len = line_inc(yytext);str = merge_string(yytext);inc_ec();errorfile<<"\nError at line no "<<lineno()-str_len<<": Unterminated Comment "<<yytext<<endl;}

{newline} {line_count++;}
<<EOF>> {return 0;}
[#$`~] {errorfile<<"\nError at line no "<<line_count<<": Unrecognized character "<<yytext<<endl<<endl;str_len = line_inc(yytext);inc_ec();}	 
. {}    

