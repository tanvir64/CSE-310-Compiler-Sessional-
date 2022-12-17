%option noyywrap yylineno

%{
#include<iostream>
#include<fstream>
#include<string>
#include "Symbol_table.cpp"

ofstream out("1705064_token.txt",ios::out);
ofstream outfile("1705064_log.txt",ios::out);
SymbolTable st(7);
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
newline [\n(\r\n)]
Digits [0-9] 
Letter [a-zA-Z]
any_char [+\-\*,\.;=\}\{\[\]?\"\/\\\']
Identifier ({Letter}|_)({Letter}|{Digits}|_)*
esc ((\\n)|(\\t)|(\\r)|(\\b)|(\\v)|(\\0)|(\\a)|(\\f)) 
Character_literals \'(({Letter}|{esc}|[+\-\*\{\}\[\];\.])|{Letter}{ws})\'
string_literals ((\"({Letter}|{ws}|{esc}|{any_char})+\")|((\")(({Letter}|{ws}|{esc}|{any_char})+(\\{newline}({Letter}|{ws}|{esc}|{any_char}))*)*\"))
Integer_literals {Digits}+
comments (((\/\*)(({ws}|{Letter}|{Digits}|{any_char}|{esc})*{newline}*({ws}|{Letter}|{Digits}|{any_char}|{esc})*)*(\*\/))|(\/\/({ws}|{Letter}|{Digits}|{any_char}|{esc})*((\\{newline})+)?(({ws}|{Letter}|{Digits}|{any_char}|{esc})*)?))
Floating_point_literals {Digits}*(\.{Integer_literals})?([Ee][+-]?{Integer_literals})?

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
(if) {out<<"<IF> "; outfile<<"\nLine no "<<yylineno<<": Token <IF> Lexeme "<<yytext<<" found"<<endl;}
(for) {out<<"<FOR> "; outfile<<"\nLine no "<<yylineno<<": Token <FOR> Lexeme "<<yytext<<" found"<<endl;}
(do) {out<<"<DO> "; outfile<<"\nLine no "<<yylineno<<": Token <DO> Lexeme "<<yytext<<" found"<<endl;}
(float) {out<<"<FLOAT> "; outfile<<"\nLine no "<<yylineno<<": Token <FLOAT> Lexeme "<<yytext<<" found"<<endl;}
(void) {out<<"<VOID> "; outfile<<"\nLine no "<<yylineno<<": Token <VOID> Lexeme "<<yytext<<" found"<<endl;}
(int) {out<<"<INT> "; outfile<<"\nLine no "<<yylineno<<": Token <INT> Lexeme "<<yytext<<" found"<<endl;}
(switch) {out<<"<SWITCH> "; outfile<<"\nLine no "<<yylineno<<": Token <SWITCH> Lexeme "<<yytext<<" found"<<endl;}
(default) {out<<"<DEFAULT> ";outfile<<"\nLine no "<<yylineno<<": Token <DEFAULT> Lexeme "<<yytext<<" found"<<endl;}
(else) {out<<"<ELSE>";outfile<<"\nLine no "<<yylineno<<": Token <ELSE> Lexeme "<<yytext<<" found"<<endl;}
(while) {out<<"<WHILE> ";outfile<<"\nLine no "<<yylineno<<": Token <WHILE> Lexeme "<<yytext<<" found"<<endl;}
(break) {out<<"<BREAK> ";outfile<<"\nLine no "<<yylineno<<": Token <BREAK> Lexeme "<<yytext<<" found"<<endl;}
(char) {out<<"<CHAR> ";outfile<<"\nLine no "<<yylineno<<": Token <CHAR> Lexeme "<<yytext<<" found"<<endl;}
(double) {out<<"<DOUBLE> ";outfile<<"\nLine no "<<yylineno<<": Token <DOUBLE> Lexeme "<<yytext<<" found"<<endl;}
(return) {out<<"<RETURN> ";outfile<<"\nLine no "<<yylineno<<": Token <RETURN> Lexeme "<<yytext<<" found"<<endl;}
(case) {out<<"<CASE> ";outfile<<"\nLine no "<<yylineno<<": Token <CASE> Lexeme "<<yytext<<" found"<<endl;}
(continue) {out<<"<CONTINUE> ";outfile<<"\nLine no "<<yylineno<<": Token <CONTINUE> Lexeme "<<yytext<<" found"<<endl;}

"++"|"--" {out<<"<INCOP, "<<yytext<<"> ";outfile<<"\nLine no "<<yylineno<<": Token <INCOP> Lexeme "<<yytext<<" found"<<endl;}
[+-] {out<<"<ADDOP, "<<yytext<<"> ";outfile<<"\nLine no "<<yylineno<<": Token <ADDOP> Lexeme "<<yytext<<" found"<<endl;}
[*/%] {out<<"<MULOP, "<<yytext<<"> ";outfile<<"\nLine no "<<yylineno<<": Token <MULOP> Lexeme "<<yytext<<" found"<<endl;}
"<"|"<="|">"|">="|"=="|"!=" {out<<"<RELOP, "<<yytext<<"> ";outfile<<"\nLine no "<<yylineno<<": Token <RELOP> Lexeme "<<yytext<<" found"<<endl;}
"!" {out<<"<NOT, "<<yytext<<"> ";outfile<<"\nLine no "<<yylineno<<": Token <NOT> Lexeme "<<yytext<<" found"<<endl;}
"=" {out<<"<ASSIGNOP, "<<yytext<<"> ";outfile<<"\nLine no "<<yylineno<<": Token <ASSIGNOP> Lexeme "<<yytext<<" found"<<endl;}
"&&"|"||" {out<<"<LOGICOP, "<<yytext<<"> ";outfile<<"\nLine no "<<yylineno<<": Token <LOGICOP> Lexeme "<<yytext<<" found"<<endl;}
"(" {out<<"<LPAREN, "<<yytext<<"> ";outfile<<"\nLine no "<<yylineno<<": Token <LPAREN> Lexeme "<<yytext<<" found"<<endl;}
")" {out<<"<RPAREN, "<<yytext<<"> ";outfile<<"\nLine no "<<yylineno<<": Token <RPAREN> Lexeme "<<yytext<<" found"<<endl;}
"{" {out<<"<LCURL, "<<yytext<<"> ";st.enter_scope();outfile<<"\nLine no "<<yylineno<<": Token <LCURL> Lexeme "<<yytext<<" found"<<endl;}
"}" {out<<"<RCURL, "<<yytext<<"> ";st.exit_scope();outfile<<"\nLine no "<<yylineno<<": Token <RCURL> Lexeme "<<yytext<<" found"<<endl;}
"[" {out<<"<LTHIRD, "<<yytext<<"> ";outfile<<"\nLine no "<<yylineno<<": Token <LTHIRD> Lexeme "<<yytext<<" found"<<endl;}
"]" {out<<"<RTHIRD, "<<yytext<<"> ";outfile<<"\nLine no "<<yylineno<<": Token <RTHIRD> Lexeme "<<yytext<<" found"<<endl;}
"," {out<<"<COMMA, "<<yytext<<"> ";outfile<<"\nLine no "<<yylineno<<": Token <COMMA> Lexeme "<<yytext<<" found"<<endl;}
";" {out<<"<SEMICOLON, "<<yytext<<"> ";outfile<<"\nLine no "<<yylineno<<": Token <SEMICOLON> Lexeme "<<yytext<<" found"<<endl;}

{Identifier} {outfile<<"\nLine no "<<yylineno<<": Token <ID> Lexeme "<<yytext<<" found"<<endl;out<<"<ID, "<<yytext<<"> ";bool b = st.insert_sym(yytext,"ID",outfile);if(b) st.print_all(outfile);}
{string_literals} {str_len = line_inc(yytext);str = merge_string(yytext);outfile<<"\nLine no "<<yylineno-str_len<<": Token <STRING> Lexeme "<<yytext<<" found --> <STRING, "<<str<<">"<<endl;out<<"<STRING, "<<str<<"> ";}
{Character_literals} {ch = change_char(yytext);outfile<<"\nLine no "<<yylineno<<": Token <CONST_CHAR> Lexeme "<<yytext<<" found --> <CONST_CHAR, "<<ch<<">"<<endl;out<<"<CONST_CHAR, "<<ch<<"> ";bool b = st.insert_sym(yytext,"CONST_CHAR",outfile);if(b) st.print_all(outfile);}
{Integer_literals}+ {outfile<<"\nLine no "<<yylineno<<": Token <CONST_INT> Lexeme "<<yytext<<" found"<<endl;out<<"<CONST_INT, "<<yytext<<"> ";bool b = st.insert_sym(yytext,"CONST_INT",outfile);if(b) st.print_all(outfile);}
{Floating_point_literals} {outfile<<"\nLine no "<<yylineno<<": Token <CONST_FLOAT> Lexeme "<<yytext<<" found"<<endl;out<<"<CONST_FLOAT, "<<yytext<<"> ";bool b = st.insert_sym(yytext,"CONST_FLOAT",outfile);if(b) st.print_all(outfile);}

{comments} {str_len = line_inc(yytext);outfile<<"\nLine no "<<yylineno-str_len<<": Token <COMMENT> Lexeme "<<yytext<<" found"<<endl;}

{decimal_point_error} {inc_ec();outfile<<"\nError at line no "<<yylineno<<": Too many decimal points "<<yytext<<endl;}
{ill_formed} {inc_ec();outfile<<"\nError at line no "<<yylineno<<": Ill formed number "<<yytext<<endl;}
{invalid} {inc_ec();outfile<<"\nError at line no "<<yylineno<<": Invalid prefix on ID or invalid suffix on Number "<<yytext<<endl;}
{multi_char_error} {inc_ec();outfile<<"\nError at line no "<<yylineno<<": Multi character constant error "<<yytext<<endl;}
{emp_char_error} {inc_ec();outfile<<"\nError at line no "<<yylineno<<": Empty character constant error "<<yytext<<endl;}
{inv_char_error} {inc_ec();outfile<<"\nError at line no "<<yylineno<<": Unterminated character "<<yytext<<endl;} 
{inv_str_error} {str_len = line_inc(yytext);str = merge_string(yytext);inc_ec();outfile<<"\nError at line no "<<yylineno-str_len<<": Unterminated String "<<yytext<<endl;}
{inv_comm_error} {str_len = line_inc(yytext);str = merge_string(yytext);inc_ec();outfile<<"\nError at line no "<<yylineno-str_len<<": Unterminated Comment "<<yytext<<endl;}

{newline} {line_count++;}
<<EOF>> {st.print_all(outfile);outfile<<"\nTotal lines: "<<line_count<<endl;
	     outfile<<"Total errors: "<<error_count<<endl; return 0;}
. {str_len = line_inc(yytext);inc_ec();outfile<<"\nError at line no "<<yylineno-str_len<<": Unrecognized character "<<yytext<<endl;}	     
%%

int main(int argc,char *argv[]){
	
	if(argc!=2){
		printf("Please provide input file name and try again\n");
		return 0;
	}
	
	FILE *fin=fopen(argv[1],"r");
	if(fin==NULL){
		printf("Cannot open specified file\n");
		return 0;
	}
	yyin= fin;
	yylex();
	fclose(yyin);
	return 0;
}
