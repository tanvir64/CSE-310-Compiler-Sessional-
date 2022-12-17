%{
#include<iostream>
#include<fstream>
#include<cstdlib>
#include<cstring>
#include<string>
#include "Symbol_table.cpp"

//#define YYSTYPE SymbolInfo*

using namespace std;

int yyparse(void);
int yylex(void);
//int yydebug = 1;
extern FILE *yyin;
extern int line_count;
extern int error_count;
extern int yylineno;
extern char* yytext;
vector<string> params[100];
int vect_no=0;
bool array_mismatch[100] = {false};
int mismatch_no = 0;
string func_name;
bool pre_enter[100] = {false};
vector<string> has_decl;
int pn = 0,pre_no = 0;

SymbolInfo* si = new SymbolInfo();
string type;
SymbolTable* st = new SymbolTable(30);
FILE *fp,*fp1,*fp2,*fp3;
ofstream logfile("log.txt",ios::out);
ofstream errorfile("error.txt",ios::out);

void yyerror(char *s)
{
	
}

bool has_entry(string s){
	int found = 0;
	if(st->lookup(s) != nullptr) {si = st->lookup(s);}
	cout<<"checking "<<s<<endl;	
	//cout<<si->get_name();
	for(int i=0;i<has_decl.size();i++){
		if(has_decl[i] == s) {
			cout<<"found "<<s<<endl;
			found = 1;
			break;
		}
	}
	if(found == 1) return true; 	
	else return false;
}

int find_length(string str){
	int n=0;
	for(int i=0;i<str.size();i++)
		if(str[i] == '\n'){			
			n++;
		}							
	return n;
}

%}

%union {double dval; int ivar; char* svar; SymbolInfo* symval; vector<string>* vect;}
%token<svar> IF ELSE FOR DO FLOAT INT VOID CHAR DOUBLE WHILE RETURN CONTINUE LPAREN RPAREN LCURL RCURL COMMA SEMICOLON LTHIRD RTHIRD PRINTLN
%token<symval> ID CONST_INT CONST_FLOAT INCOP DECOP ADDOP MULOP RELOP LOGICOP ASSIGNOP 
%token<svar> NOT
%type<svar> type_specifier
%type<symval> var_declaration unit program start func_declaration func_definition compound_statement parameter_list variable factor unary_expression term simple_expression rel_expression id declaration_list logic_expression expression expression_statement statement statements argument_list arguments
%left ADDOP
%right MULOP NOT
%nonassoc LOWER_THAN_ELSE
%nonassoc ELSE

%%

start : program {logfile<<"Line "<<line_count-1<<": start : program"<<endl<<endl;}	
	;

program : program unit  {			
			$$->set_name($1->get_name()+"\n"+$2->get_name());
			logfile<<"\nLine "<<line_count<<": program : program unit"<<endl<<endl<<$$->get_name()<<endl<<endl;
		}
	| unit {
		$$ = $1;
		logfile<<"\nLine  "<<line_count<<": program : unit"<<endl<<endl<<$$->get_name()<<endl<<endl;
	}
	;
	
unit : var_declaration {		
			$$ = $1;
			logfile<<"\nLine  "<<line_count<<": unit : var_declaration"<<endl<<endl<<$$->get_name()<<endl<<endl;
		}
     | func_declaration {		
			$$ = $1;
			logfile<<"\nLine  "<<line_count<<": unit : func_declaration"<<endl<<endl<<$$->get_name()<<endl<<endl;
		 }
     | func_definition {
     		$$ = $1;
			logfile<<"\nLine  "<<line_count<<": unit : func_definition"<<endl<<endl<<$$->get_name()<<endl<<endl;
     	}
     ;

id : ID {
		$$ = new SymbolInfo();
		func_name = $1->get_name();
		$$->set_name(func_name);
		$$->set_type("ID");
	}
	;

pre_enter_func_name : {						
		if(st->lookup(func_name) == nullptr) {			
			si = new SymbolInfo(func_name,"ID");
			cout<<"pre enter "<<func_name<<" "<<si<<endl;;
			bool b = st->insert_sym(si);
			pre_enter[pre_no] = true;			
			pn = pre_no;						
			pre_no++;							
		}
		else{
			pn = pre_no++;
		}							
		//cout<<"pn"<<pn;		
	}
	;
	     	 
func_declaration : type_specifier id pre_enter_func_name LPAREN parameter_list RPAREN SEMICOLON {
			$$ = new SymbolInfo();
			string emp = " ";			
			$$->set_name($1+emp+$2->get_name()+"("+$5->get_name()+");");
			//cout<<$2->get_name();
			if(st->lookup($2->get_name()) != nullptr) {si = st->lookup($2->get_name());}			
			int p = params[vect_no].size();						
			for(int i=0;i<p;i++) {
				string var = params[vect_no][i];
				if(st->current_lookup(var) != nullptr)
					st->remove_sym(var);									
			}
			params[vect_no].clear();
			st->exit_scope(logfile);
			vect_no++;								
			if(pre_enter[pn] == false){
				//si = st->lookup($2->get_name());
				if(si->get_vartype() == "function"){
					errorfile<<"Error at line "<<line_count<<" : Redeclaration of function "<<si->get_name()<<endl<<endl; error_count++;
					logfile<<"Error at line "<<line_count<<" : Redeclaration of function "<<si->get_name()<<endl<<endl;
				}
				else{
					errorfile<<"Error at line "<<line_count<<" : Multiple declaration of "<<si->get_name()<<endl<<endl; error_count++;
					logfile<<"Error at line "<<line_count<<" : Multiple declaration of "<<si->get_name()<<endl<<endl;
				}
			}
			else{
				cout<<"in dec "<<$2->get_name()<<endl;				
				cout<<si<<endl;								
				if(strcmp($1,"int") == 0) {si->set_idtype("CONST_INT");}
				else if(strcmp($1,"float") == 0) {si->set_idtype("CONST_FLOAT");}
				else if(strcmp($1,"void") == 0) {si->set_idtype("VOID");}
				si->set_vartype("function");
				si->fp = new FuncAttribute();
				si->fp->set_rettype($1);
				si->fp->set_decltype("dec");
				has_decl.push_back($2->get_name());	
				//cout<<si->fp->get_rettype();														
				char* str = new char[$5->get_name().length()+1];
				strcpy(str,$5->get_name().c_str());
				char* token = new char[$5->get_name().length()];
				token = strtok(str," ,");
				int count = 1;
				while(token != NULL){					
					if(strcmp(token,"int") == 0) {si->fp->param_list.push_back("CONST_INT");}
					else if(strcmp(token,"float") == 0){si->fp->param_list.push_back("CONST_FLOAT");}
					else{
						for(int i=0;token[i];i++){
							if(token[i] == '[') count++;
							if(token[i] == ']') count++;							
						}
						if(count > 1)  {si->fp->param_type.push_back("array");}
						else {si->fp->param_type.push_back("var");}	
					}
					token = strtok(NULL," ,");
				}				
			}		 												
			logfile<<"Line  "<<line_count<<": func_declaration : type_specifier ID LPAREN parameter_list RPAREN SEMICOLON"<<endl<<endl<<$$->get_name()<<endl<<endl;			
		}
		| type_specifier id pre_enter_func_name LPAREN RPAREN SEMICOLON {
			$$ = new SymbolInfo();
			string emp = " ";	
			$$->set_name($1+emp+$2->get_name()+"("+");");
			if(st->lookup($2->get_name()) != nullptr) {si = st->lookup($2->get_name());}
			if(pre_enter[pn] == false){				
				if(si->get_vartype() == "function"){
					errorfile<<"Error at line "<<line_count<<" : Redeclaration of function "<<si->get_name()<<endl<<endl; error_count++;
					logfile<<"Error at line "<<line_count<<" : Redeclaration of function "<<si->get_name()<<endl<<endl;
				}
				else{
					errorfile<<"Error at line "<<line_count<<" : Multiple declaration of "<<si->get_name()<<endl<<endl; error_count++;
					logfile<<"Error at line "<<line_count<<" : Multiple declaration of "<<si->get_name()<<endl<<endl;
				}
			}
			else{										
				if(strcmp($1,"int") == 0) si->set_idtype("CONST_INT");
				else if(strcmp($1,"float") == 0) si->set_idtype("CONST_FLOAT");
				else if(strcmp($1,"void") == 0) si->set_idtype("VOID");
				si->set_vartype("function");
				si->fp = new FuncAttribute();
				si->fp->set_rettype($1);
				si->fp->set_decltype("dec");	
				has_decl.push_back($2->get_name());							
			}					
			logfile<<"Line  "<<line_count<<": func_declaration : type_specifier ID LPAREN RPAREN SEMICOLON"<<endl<<endl<<$$->get_name()<<endl<<endl;	
		}
		;
	 	
func_definition : type_specifier id pre_enter_func_name LPAREN parameter_list RPAREN compound_statement{			
			$$ = new SymbolInfo();			
			string emp = " ";
			$$->set_name($1+emp+$2->get_name()+"("+$5->get_name()+")"+$7->get_name());
			if(st->lookup($2->get_name()) != nullptr) {si = st->lookup($2->get_name());}
			cout<<$2->get_name()<<si<<endl;			
			//if(has_entry($2->get_name())) {si = st->lookup($2->get_name());cout<<si<<endl;}			
			if(has_entry($2->get_name()) || (has_entry($2->get_name()) == false && pre_enter[pn] == false)){								
				cout<<"in error detection "<<$2->get_name()<<" "<<si->fp->get_decltype()<<endl;											
				//if function previously defined
				if(si->get_vartype() == "function" && si->fp->get_decltype() == "def"){
					errorfile<<"Error at line "<<line_count-find_length($7->get_name())<<" : Redefinition of function "<<si->get_name()<<endl<<endl; error_count++;
					logfile<<"Error at line "<<line_count-find_length($7->get_name())<<" : Redefinition of function "<<si->get_name()<<endl<<endl;
				}
				// if function previously declared
				else if(si->get_vartype() == "function" && si->fp->get_decltype() == "dec"){
					int param = si->fp->param_no();
					//cout<<param;
					//cout<<si->fp->get_rettype();
					if(si->fp->get_rettype() != $1){
						logfile<<"Error at line "<<line_count-find_length($7->get_name())<<" : Return type mismatch with function declaration in function "<<$2->get_name()<<endl<<endl;	
						errorfile<<"Error at line "<<line_count-find_length($7->get_name())<<" : Return type mismatch with function declaration in function "<<$2->get_name()<<endl<<endl;error_count++;
					}
					else{
						char* str = new char[$5->get_name().length()+1];
						strcpy(str,$5->get_name().c_str());
						char* token = new char[$5->get_name().length()];
						token = strtok(str," ,");						
						vector<string> param_vect;
						vector<string> type_vect;
						while(token != NULL){					
							if(strcmp(token,"int") == 0){
								param_vect.push_back("CONST_INT");
							}							
							else if(strcmp(token,"float") == 0){
								param_vect.push_back("CONST_FLOAT");
							}
							else{								
								if(st->current_lookup(token) != nullptr){
									SymbolInfo* sym = st->current_lookup(token);
									type_vect.push_back(sym->get_vartype());
								}									
							}
							token = strtok(NULL," ,");
						}
						delete[] str;
						delete[] token;
						if(param_vect.size() != param){
							logfile<<"Error at line "<<line_count-find_length($7->get_name())<<" : Total number of arguments mismatch with declaration in function "<<si->get_name()<<endl<<endl;
	 						errorfile<<"Error at line "<<line_count-find_length($7->get_name())<<" : Total number of arguments mismatch with declaration in function "<<si->get_name()<<endl<<endl; error_count++;
						}
						else{
							int found = 0;
							for(int i=0;i<type_vect.size();i++){
								if(type_vect[i] != si->fp->param_type[i]){
									logfile<<"Error at line "<<line_count<<" : "<<i+1<<"th argument mismatch in function "<<si->get_name()<<endl<<endl;
	 								errorfile<<"Error at line "<<line_count<<" : "<<i+1<<"th argument mismatch in function "<<si->get_name()<<endl<<endl; error_count++;
	 								found = 1;
								}
								if(found = 1) break;
							}
						}
					}					
				}
				// if function name and global variable has same name
				else if(si->get_vartype() != "function"){
					errorfile<<"Error at line "<<line_count-find_length($7->get_name())<<" : Multiple declaration of "<<si->get_name()<<endl<<endl; error_count++;
					logfile<<"Error at line "<<line_count-find_length($7->get_name())<<" : Multiple declaration of "<<si->get_name()<<endl<<endl;
				}
			}
			else{							
				if(strcmp($1,"int") == 0) si->set_idtype("CONST_INT");
				else if(strcmp($1,"float") == 0) si->set_idtype("CONST_FLOAT");
				else if(strcmp($1,"void") == 0) si->set_idtype("VOID");
				si->set_vartype("function");
				si->fp = new FuncAttribute();
				si->fp->set_rettype($1);
				si->fp->set_decltype("def");			
				char* str = new char[$5->get_name().length()+1];
				strcpy(str,$5->get_name().c_str());
				char* token = new char[$5->get_name().length()];
				token = strtok(str," ,");
				int count=1;
				while(token != NULL){										
					if(strcmp(token,"int") == 0) {si->fp->param_list.push_back("CONST_INT");}
					else if(strcmp(token,"float") == 0){si->fp->param_list.push_back("CONST_FLOAT");}
					else{
						for(int i=0;token[i];i++){
							if(token[i] == '[') count++;
							if(token[i] == ']') count++;							
						}
						if(count > 1)  {si->fp->param_type.push_back("array");}
						else {si->fp->param_type.push_back("var");}	
					}
					token = strtok(NULL," ,");
				}				
				for(int i=0;i<si->fp->param_type.size();i++){
					if(si->fp->param_type[i] == ""){
						errorfile<<"Error at line "<<line_count<<" : "<<i+1<<"th parameter's name not given in function definition of"<<$2->get_name()<<endl<<endl; error_count++;
					logfile<<"Error at line "<<line_count<<" : "<<i+1<<"th parameter's name not given in function definition of"<<$2->get_name()<<endl<<endl;
					}
				}				
			}
			logfile<<"Line "<<line_count<<": func_definition : type_specifier ID LPAREN parameter_list RPAREN compound_statement"<<endl<<endl<<$$->get_name()<<endl<<endl;		
		}
		| type_specifier id pre_enter_func_name LPAREN RPAREN compound_statement {
			$$ = new SymbolInfo();
			string emp = " ";				
			$$->set_name($1+emp+$2->get_name()+"("+")"+$6->get_name());	
			if(st->lookup($2->get_name()) != nullptr) {si = st->lookup($2->get_name());}		
			if(has_entry($2->get_name()) || (has_entry($2->get_name()) == false && pre_enter[pn]==false)){				
				// if function previously defined
				if(si->get_vartype() == "function" && si->fp->get_decltype() == "def"){
					errorfile<<"Error at line "<<line_count-find_length($6->get_name())<<" : Redeclaration of function "<<si->get_name()<<endl<<endl; error_count++;
					logfile<<"Error at line "<<line_count-find_length($6->get_name())<<" : Redeclaration of function "<<si->get_name()<<endl<<endl;
				}
				// if function previously declared
				else if(si->get_vartype() == "function" && si->fp->get_decltype() == "dec"){
					int param = si->fp->param_no();
					if(si->fp->get_rettype() != $1){
						logfile<<"Error at line "<<line_count-find_length($6->get_name())<<" : Return type mismatch with function declaration in function "<<$2->get_name()<<endl<<endl;	
						errorfile<<"Error at line "<<line_count-find_length($6->get_name())<<" : Return type mismatch with function declaration in function "<<$2->get_name()<<endl<<endl;error_count++;
					}					
				}
				// if function name and global variable has same name
				else if(si->get_vartype() != "function"){
					errorfile<<"Error at line "<<line_count-find_length($6->get_name())<<" : Multiple declaration of "<<si->get_name()<<endl<<endl; error_count++;
					logfile<<"Error at line "<<line_count-find_length($6->get_name())<<" : Multiple declaration of "<<si->get_name()<<endl<<endl;
				}
			}
			else{	
				//cout<<"in def "<<$2->get_name()<<endl;
				if(strcmp($1,"int") == 0) si->set_idtype("CONST_INT");
				else if(strcmp($1,"float") == 0) si->set_idtype("CONST_FLOAT");
				else if(strcmp($1,"void") == 0) si->set_idtype("VOID");
				si->set_vartype("function");
				si->fp = new FuncAttribute();
				si->fp->set_rettype($1);
				//cout<<si->fp->get_rettype();	
				si->fp->set_decltype("def");	
			}
			logfile<<"Line "<<line_count<<": func_definition : type_specifier ID LPAREN RPAREN compound_statement"<<endl<<endl<<$$->get_name()<<endl<<endl;		
		}
 		;				

parameter_list  : parameter_list COMMA type_specifier id {
			$$ = new SymbolInfo();				
			string str = " ";
			$$->set_name($1->get_name()+","+$3+str+$4->get_name());
			logfile<<"Line  "<<line_count<<": parameter_list : parameter_list COMMA type_specifier ID"<<endl<<endl;
			if(st->current_lookup($4->get_name()) != nullptr){
	  			errorfile<<"Error at line "<<line_count<<" : Multiple declaration of "<< ($4->get_name())<<" in parameter"<<endl<<endl;error_count++;	
	  			logfile<<"Error at line "<<line_count<<" : Multiple declaration of "<< ($4->get_name())<<" in parameter"<<endl<<endl;	   			
	  		}	  			  		
	  		else{
		  		SymbolInfo* id = new SymbolInfo();
		  		id->set_name($4->get_name()); id->set_type("ID"); 
		  		if(strcmp($3,"int") == 0) {id->set_idtype("CONST_INT");}
				else if(strcmp($3,"float") == 0) {id->set_idtype("CONST_FLOAT");}
				else if(strcmp($3,"void") == 0) {
					errorfile<<"Error at line "<<line_count<<" : Variable type cannot be void"<<endl<<endl;error_count++;	 
  					logfile<<"Error at line "<<line_count<<" : Variable type cannot be void"<<endl<<endl;
				}
				id->set_vartype("var");
		  		bool b = st->insert_sym(id);		  						
			}
			params[vect_no].push_back($4->get_name());
			logfile<<$$->get_name()<<endl<<endl;
		}
		| parameter_list COMMA type_specifier {
			$$ = new SymbolInfo();				
			$$->set_name($1->get_name()+","+$3);
			logfile<<"Line  "<<line_count<<": parameter_list : parameter_list COMMA type_specifier"<<endl<<endl<<$$->get_name()<<endl<<endl;
		}
 		| type_specifier id { 						
 			$$ = new SymbolInfo();
 			string str = " ";
 			$$->set_name($1+str+$2->get_name()); 			 			
 			st->enter_scope(logfile);
 			logfile<<"Line  "<<line_count<<": parameter_list : type_specifier ID"<<endl<<endl;
 			if(st->current_lookup($2->get_name()) != nullptr){
	  			errorfile<<"Error at line "<<line_count<<" : Multiple declaration of "<< ($2->get_name())<<" in parameter"<<endl<<endl;error_count++;	  	
	  			logfile<<"Error at line "<<line_count<<" : Multiple declaration of "<< ($2->get_name())<<" in parameter"<<endl<<endl;		
	  		}  			  		
	  		else{
		  		SymbolInfo* id = new SymbolInfo();
		  		id->set_name($2->get_name()); id->set_type("ID");
		  		//cout<<$1<<" "<<$2->get_name()<<endl; 
		  		if(strcmp($1,"int") == 0) {id->set_idtype("CONST_INT");}
				else if(strcmp($1,"float") == 0) {id->set_idtype("CONST_FLOAT");}
				else if(strcmp($1,"void") == 0) {
					errorfile<<"Error at line "<<line_count<<" : Variable type cannot be void"<<endl<<endl;error_count++;	 
  					logfile<<"Error at line "<<line_count<<" : Variable type cannot be void"<<endl<<endl;
				}
				id->set_vartype("var");
		  		bool b = st->insert_sym(id);													
			}
			params[vect_no].push_back($2->get_name());
			logfile<<$$->get_name()<<endl<<endl;
 		}
		| type_specifier {
			$$ = new SymbolInfo();			
			$$->set_name($1);
			logfile<<"Line  "<<line_count<<": parameter_list : type_specifier"<<endl<<endl<<$$->get_name()<<endl<<endl;
			if($1 != "int" || $1 != "float"){
				errorfile<<"Error at line "<<line_count<<" : Syntax error"<<endl<<endl;error_count++;	  	
	  			logfile<<"Error at line "<<line_count<<" : Syntax error"<<endl<<endl<<$1<<endl<<endl;	
	  			string str($1);
				int int_pos = str.find("int");
				int float_pos = str.find("float");
				if(int_pos != -1) {$$->set_name("int");}
				else if(float_pos != -1) {$$->set_name("float");}  			
			}							
		}
 		;

compound_statement : LCURL {if(params[vect_no].size() == 0){st->enter_scope(logfile);}} statements RCURL{				
			$$ = new SymbolInfo();											
			$$->set_name("{\n"+$3->get_name()+"\n}");	
			//cout<<$$->get_name();							
			//for(int i=0;i<params[vect_no].size();i++){cout<<params[vect_no][i];}				
			logfile<<"Line  "<<line_count<<": compound_statement : LCURL statements RCURL"<<endl<<endl<<$$->get_name()<<endl<<endl;								
			st->print_all(logfile);
			st->exit_scope(logfile);
			vect_no++;				
		}
	    | LCURL {if(params[vect_no].size() == 0) {st->enter_scope(logfile);}} RCURL {
	 		 $$ = new SymbolInfo();
	 		 string str($1);
	 		 $$->set_name($1);		 		 
	 		 st->print_all(logfile);
	 		 st->exit_scope(logfile);
	 		 vect_no++; 		    	 		   
	    }
	    ;
 		    
var_declaration : type_specifier declaration_list SEMICOLON{
			$$ = new SymbolInfo();
			string emp = " ";
			$$->set_name($1+emp+$2->get_name()+";");			
			char* str = new char[$2->get_name().length()+1];
			strcpy(str,$2->get_name().c_str());									
			char* token = new char[$2->get_name().length()];
			token = strtok(str,",[][0-9] ");
			char* type = $1;
			logfile<<"Line  "<<line_count<<": var_declaration : type_specifier declaration_list SEMICOLON"<<endl<<endl;									
			while(token != NULL){															
				if(st->current_lookup(token) != nullptr){					
					si = st->current_lookup(token);										
					if(si->get_idtype() == ""){
						if(strcmp(type,"int") == 0) {si->set_idtype("CONST_INT");}
						else if(strcmp(type,"float") == 0) {si->set_idtype("CONST_FLOAT");}
						else if(strcmp(type,"void") == 0) {
							errorfile<<"Error at line "<<line_count<<" : Variable type cannot be void"<<endl<<endl;error_count++;	 
		  					logfile<<"Error at line "<<line_count<<" : Variable type cannot be void"<<endl<<endl;
						}
					}
				}
				else if(st->lookup(token) != nullptr){					
					si = st->lookup(token);										
					if(si->get_idtype() == ""){
						if(strcmp(type,"int") == 0) {si->set_idtype("CONST_INT");}
						else if(strcmp(type,"float") == 0) {si->set_idtype("CONST_FLOAT");}
						else if(strcmp(type,"void") == 0) {
							errorfile<<"Error at line "<<line_count<<" : Variable type cannot be void"<<endl<<endl;error_count++;	 
		  					logfile<<"Error at line "<<line_count<<" : Variable type cannot be void"<<endl<<endl;
						}
					}
				}																	
				token = strtok(NULL,",[][0-9] ");
			}														
			logfile<<$$->get_name()<<endl<<endl;		
		}
 		 ;
 		 
type_specifier : INT {
					$$ = "int";
					type = "int";
					logfile<<"Line "<<line_count<<": type_specifier : INT"<<endl<<endl<<$$<<endl<<endl; }
 		| FLOAT {
					$$ = "float";
					type = "float";
					logfile<<"Line "<<line_count<<": type_specifier : FLOAT"<<endl<<endl<<$$<<endl<<endl; }
 		| VOID {
					$$ = "void";
					type = "void";
					logfile<<"Line "<<line_count<<": type_specifier : VOID"<<endl<<endl<<$$<<endl<<endl; }
 		;
 		
declaration_list : declaration_list COMMA id {	
			$$ = new SymbolInfo();
			$$->set_name($1->get_name()+","+$3->get_name());
 		  	//$$ = new vector<string>();			  	
		  	if(st->current_lookup($3->get_name()) != nullptr){
	  			errorfile<<"Error at line "<<line_count<<" : Multiple declaration of "<< ($3->get_name())<<endl<<endl;error_count++;	 
	  			logfile<<"Error at line "<<line_count<<" : Multiple declaration of "<< ($3->get_name())<<endl<<endl; 		
	  		}
	  		else{
	  			SymbolInfo* id = new SymbolInfo();
		  		id->set_name($3->get_name()); id->set_type("ID");
		  		id->set_vartype("var");
		  		bool b = st->insert_sym(id);
	  		}	  			  			  		  		
	  		logfile<<"Line  "<<line_count<<" declaration_list : declaration_list COMMA ID"<<endl<<endl<<$$->get_name()<<endl<<endl; 
		  }
 		  | declaration_list COMMA id LTHIRD CONST_INT RTHIRD 
 		  { 
 		  	$$ = new SymbolInfo();
 		  	$$->set_name($1->get_name()+","+$3->get_name()+"["+$5->get_name()+"]");		  	
	  		if(st->current_lookup($3->get_name()) != nullptr){
	  			errorfile<<"Error at line "<<line_count<<" : Multiple declaration of "<< ($3->get_name())<<endl<<endl;error_count++;
	  			logfile<<"Error at line "<<line_count<<" : Multiple declaration of "<< ($3->get_name())<<endl<<endl;	  			
	  		}
	  		else{
		  		SymbolInfo* id = new SymbolInfo();
		  		id->set_name($3->get_name()); id->set_type("ID"); 
		  		id->set_vartype("array");
		  		bool b = st->insert_sym(id);
		  	}
			logfile<<"Line "<<line_count<<": declaration_list : declaration_list COMMA ID LTHIRD CONST_INT RTHIRD"<<endl<<endl<<$$->get_name()<<endl<<endl;					  			
 		  }
 		  | id { 
 		  	$$ = new SymbolInfo();
 		  	$$->set_name($1->get_name());		  	
	  		if(st->current_lookup($1->get_name()) != nullptr){
	  			errorfile<<"Error at line "<<line_count<<" : Multiple declaration of "<< ($1->get_name())<<endl<<endl;error_count++;	 
	  			logfile<<"Error at line "<<line_count<<" : Multiple declaration of "<< ($1->get_name())<<endl<<endl; 			
	  		}
	  		else{	  		
		  		SymbolInfo* id = new SymbolInfo();
		  		id->set_name($1->get_name()); id->set_type("ID");
		  		id->set_vartype("var");
		  		bool b = st->insert_sym(id);
		  	}
			logfile<<"Line "<<line_count<<": declaration_list : ID"<<endl<<endl<<$$->get_name()<<endl<<endl;					  			
 		  }
 		  | id LTHIRD CONST_INT RTHIRD 
 		  { 
 		  	$$ = new SymbolInfo(); 		  	
	  		$$->set_name($1->get_name()+"["+$3->get_name()+"]");
	  		if(st->current_lookup($1->get_name()) != nullptr){
	  			errorfile<<"Error at line "<<line_count<<" : Multiple declaration of "<< ($1->get_name())<<endl<<endl; error_count++;	 
	  			logfile<<"Error at line "<<line_count<<" : Multiple declaration of "<< ($1->get_name())<<endl<<endl; 			
	  		}
	  		else{
		  		SymbolInfo* id = new SymbolInfo();
		  		id->set_name($1->get_name()); id->set_type("ID"); 
		  		id->set_vartype("array");
		  		bool b = st->insert_sym(id);
		  	}
			logfile<<"Line "<<line_count<<": declaration_list : ID LTHIRD CONST_INT RTHIRD"<<endl<<endl<<$$->get_name()<<endl<<endl;					  			  
		  }
 		  ;
 		  
statements : statements statement {
	 	$$ = new SymbolInfo();
	 	$$->set_name($1->get_name()+"\n"+$2->get_name());
	 	logfile<<"Line "<<line_count<<": statements : statements statement"<<endl<<endl<<$$->get_name()<<endl<<endl;
	 }
		| statement {
	 	$$ = new SymbolInfo();
	 	$$ = $1;
	 	logfile<<"Line "<<line_count<<": statements : statement"<<endl<<endl<<$$->get_name()<<endl<<endl;
	 }
	 ;
	   
statement : var_declaration {
	 	$$ = new SymbolInfo();
	 	$$ = $1;
	 	logfile<<"Line "<<line_count<<": statement : var_declaration"<<endl<<endl<<$$->get_name()<<endl<<endl;
	 }
	  | expression_statement {
	 	$$ = new SymbolInfo();
	 	$$ = $1;
	 	logfile<<"Line "<<line_count<<": statement : expression_statement"<<endl<<endl<<$$->get_name()<<endl<<endl;
	 }
	  | compound_statement {
	 	$$ = new SymbolInfo();
	 	$$ = $1;
	 	logfile<<"Line "<<line_count<<": statement : compound_statement"<<endl<<endl<<$$->get_name()<<endl<<endl;
	 }
	  | FOR LPAREN expression_statement expression_statement expression RPAREN statement {
	 	$$ = new SymbolInfo();
	 	string str($1);
	 	$$->set_name("for("+$3->get_name()+$4->get_name()+$5->get_name()+")"+$7->get_name());
	 	logfile<<"Line "<<line_count<<": statement : FOR LPAREN expression_statement expression_statement expression RPAREN statement"<<endl<<endl<<$$->get_name()<<endl<<endl;
	 }
	  | IF LPAREN expression RPAREN statement %prec LOWER_THAN_ELSE {
	 	$$ = new SymbolInfo();	 		 	
	 	$$->set_name("if("+$3->get_name()+")"+$5->get_name());
	 	logfile<<"Line "<<line_count<<": statement : IF LPAREN expression RPAREN statement"<<endl<<endl<<$$->get_name()<<endl<<endl;
	 }
	  | IF LPAREN expression RPAREN statement ELSE statement {
	 	$$ = new SymbolInfo();
	 	$$->set_name("if("+$3->get_name()+")"+$5->get_name()+"else"+$7->get_name());
	 	logfile<<"Line "<<line_count<<": statement : IF LPAREN expression RPAREN statement ELSE statement"<<endl<<endl<<$$->get_name()<<endl<<endl;
	 }
	  | WHILE LPAREN expression RPAREN statement {
	 	$$ = new SymbolInfo();
	 	$$->set_name("while("+$3->get_name()+")"+$5->get_name());
	 	logfile<<"Line "<<line_count<<": statement : WHILE LPAREN expression RPAREN statement"<<endl<<endl<<$$->get_name()<<endl<<endl;
	 }
	  | PRINTLN LPAREN id RPAREN SEMICOLON {
	 	$$ = new SymbolInfo();
	 	$$->set_name("printf("+$3->get_name()+");");
	 	logfile<<"Line "<<line_count<<": statement : PRINTLN LPAREN ID RPAREN SEMICOLON"<<endl<<endl;
	 	if(st->lookup($3->get_name()) == nullptr){
	 		errorfile<<"Error at line "<<line_count<<" : Undeclared variable "<< ($3->get_name())<<endl<<endl;error_count++;	
  			logfile<<"Error at line "<<line_count<<" : Undeclared variable "<< ($3->get_name())<<endl<<endl;  
	 	}
	 	logfile<<$$->get_name()<<endl<<endl;
	 }
	  | RETURN expression SEMICOLON {
	 	$$ = new SymbolInfo();	 	
	 	$$->set_name($1);
	 	logfile<<"Line "<<line_count<<": statement : RETURN expression SEMICOLON"<<endl<<endl<<$$->get_name()<<endl<<endl;
	 }
	  ;
	  
expression_statement : SEMICOLON {
	 	$$ = new SymbolInfo();
	 	$$->set_name(";"); 		 	
	 } 			
	 | expression SEMICOLON {
	 	$$ = new SymbolInfo();
	 	$$->set_name($1->get_name()+";");
	 	logfile<<"Line "<<line_count<<": expression_statement : expression SEMICOLON"<<endl<<endl<<$$->get_name()<<endl<<endl;
	 } 
	 ;
	  
variable : id {
	 	$$ = new SymbolInfo();	 	
	 	$$->set_name($1->get_name());
	 	if(st->lookup($1->get_name()) == nullptr){
  			errorfile<<"Error at line "<<line_count<<" : Undeclared variable "<< ($1->get_name())<<endl<<endl;error_count++;	
  			logfile<<"Error at line "<<line_count<<" : Undeclared variable "<< ($1->get_name())<<endl<<endl;  				  		
  		}  		
  		else{
  			$$ = $1;
  			si = st->lookup($1->get_name());
  			logfile<<"Line "<<line_count<<": variable : ID"<<endl<<endl;
  			string str($1->get_name());
  			if(si->get_vartype() == "array" && str.length() == 1 ){
  				array_mismatch[mismatch_no] = true;
  				errorfile<<"Error at line "<<line_count<<" : Type Mismatch, "<<$1->get_name()<<" is an array"<<endl<<endl; error_count++;
				logfile<<"Error at line "<<line_count<<" : Type Mismatch, "<<$1->get_name()<<" is an array"<<endl<<endl;
  			}
	  		$$->set_type(si->get_idtype());
	  		$$->set_vartype(si->get_vartype());
  		}	  		
	 	logfile<<$$->get_name()<<endl<<endl;
	 }		
	 | id LTHIRD expression RTHIRD {
	 	$$ = new SymbolInfo();
	 	$$->set_name($1->get_name()+"["+$3->get_name()+"]");
	 	if(st->lookup($1->get_name()) == nullptr){
  			errorfile<<"Error at line "<<line_count<<" : Undeclared variable "<< ($1->get_name())<<endl<<endl;error_count++;	
  			logfile<<"Error at line "<<line_count<<" : Undeclared variable "<< ($1->get_name())<<endl<<endl;
  			 		
  		}
	 	else{
	 		//$$->set_name($1->get_name()+"["+$3->get_name()+"]");
	 		si = st->lookup($1->get_name());
	 		$$->set_type(si->get_idtype());		 	
		 	//si = st->lookup(si->get_name());
		 	//$$->set_idtype(si->get_idtype());	
		 	$$->set_vartype("var"); 			 	
		 	logfile<<"Line "<<line_count<<": variable : ID LTHIRD expression RTHIRD"<<endl<<endl;
		 	if(si->get_vartype() != "array"){
		 		errorfile<<"Error at line "<<line_count<<" : "<<$1->get_name()<<" not an array"<<endl<<endl;error_count++;
		 		logfile<<"Error at line "<<line_count<<" : "<<$1->get_name()<<" not an array"<<endl<<endl;
		 	}
		 	else if($3->get_type() != "CONST_INT"){
		 		errorfile<<"Error at line "<<line_count<<" : Expression inside third brackets not an integer"<<endl<<endl;error_count++;
		 		logfile<<"Error at line "<<line_count<<" :Expression inside third brackets not an integer"<<endl<<endl;
		 	}		 	
	 	}
	 	logfile<<$$->get_name()<<endl<<endl; 
	 } 
	 ;
	 
expression : logic_expression {
	 	$$ = new SymbolInfo();
	 	$$ = $1;
	 	logfile<<"Line  "<<line_count<<" expression : logic_expression"<<endl<<endl<<$$->get_name()<<endl<<endl;
	 }
	   | variable ASSIGNOP logic_expression {
	 	$$ = new SymbolInfo();
	 	//cout<<"line"<<line_count<<" "<<$3->get_name()<<" "<<$3->get_type()<<endl;	 	
	 	$$->set_name($1->get_name()+$2->get_name()+$3->get_name());		
	 	logfile<<"Line "<<line_count<<": expression : variable ASSIGNOP logic_expression"<<endl<<endl;
		string str = $1->get_name();
		string token = "";
		int pos = str.find("[");
		if(pos != -1){
			for(int i=0;i<pos;i++){
				token += str[i];
			}
		}		
		else {token = $1->get_name();}
	 	if(st->lookup(token) != nullptr){	 		
	 		si = st->lookup(token);	 		
	 		//cout<<token<<" "<<si->get_vartype()<<endl;
		 	string var_type = si->get_idtype();
		 	//cout<<"line"<<line_count<<" "<<$1->get_name()<<" "<<var_type<<endl;
		 	if($3->get_type() == "VOID" || $1->get_type() == "VOID"){
				errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
				logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;
				$$->set_type($1->get_type());
			}			
		 	else if($3->get_type() != "undefined"){
		 		si = st->lookup(token);		 		
		 		if($3->get_type() != "undeclared"){
		 			if(var_type == "CONST_FLOAT" && ($3->get_type() == "CONST_INT" || $3->get_type() == "CONST_FLOAT")){
		 				//cout<<"ok"<<endl;
		 			}
		 			else if(var_type != $3->get_type()){
			 			cout<<line_count<<":"<<var_type<<"->"<<$3->get_type()<<endl;			 	
				 		errorfile<<"Error at line "<<line_count<<" : Type Mismatch "<<endl<<endl;
				 		logfile<<"Error at line "<<line_count<<" : Type Mismatch "<<endl<<endl;
				 		error_count++;
				 	}
			 	}			 	
			 	$$->set_type($1->get_type());
		 	}	 		
	 	}	 		 		 		 	
	 	logfile<<$$->get_name()<<endl<<endl;
	 }	
	   ;
			
logic_expression : rel_expression {
	 	$$ = new SymbolInfo();
	 	$$ = $1;
	 	//cout<<$1->get_name()<<$1->get_type()<<endl;
	 	logfile<<"Line "<<line_count<<": logic_expression : rel_expression"<<endl<<endl<<$$->get_name()<<endl<<endl;
	 }
	 | rel_expression LOGICOP rel_expression {
	 	$$ = new SymbolInfo();
	 	$$->set_name($1->get_name()+$2->get_name()+$3->get_name());
	 	logfile<<"Line "<<line_count<<": logic_expression : LOGICOP rel_expression"<<endl<<endl;
	 	if(($1->get_type() == "CONST_INT" || $1->get_type() == "CONST_FLOAT") && ($1->get_type() == "CONST_INT" || $1->get_type() == "CONST_FLOAT")) {$$->set_type("CONST_INT");}
	 	if($3->get_type() == "VOID" || $1->get_type() == "VOID"){
			errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
			logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;
			$$->set_type($1->get_type());
		}
		else if($1->get_type() == "VOID" || $3->get_type() == "VOID"){
			errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
			logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;
			$$->set_type($3->get_type());
		} 
	 	logfile<<$$->get_name()<<endl<<endl;
	 }
	;
			
rel_expression : simple_expression {
	 	$$ = new SymbolInfo();
	 	$$ = $1;
	 	//cout<<$1->get_name()<<$1->get_type()<<endl;
	 	logfile<<"Line "<<line_count<<": rel_expression : simple_expression"<<endl<<endl<<$$->get_name()<<endl<<endl;
	 }		
	| simple_expression RELOP simple_expression {
	 	$$ = new SymbolInfo();
	 	$$->set_name($1->get_name()+$2->get_name()+$3->get_name());
	 	if(($1->get_type() == "CONST_INT" || $1->get_type() == "CONST_FLOAT") && ($1->get_type() == "CONST_INT" || $1->get_type() == "CONST_FLOAT")) {$$->set_type("CONST_INT");$$->set_idtype("CONST_INT");}
	 	logfile<<"Line "<<line_count<<": rel_expression : simple_expression RELOP simple_expression"<<endl<<endl;
	 	if($1->get_type() == "VOID" || $3->get_type() == "VOID"){
			errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
			logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;
			$$->set_type($1->get_type());
		}
	 	logfile<<$$->get_name()<<endl<<endl;
	 } 	
	;
				
simple_expression : term {
	 	$$ = new SymbolInfo();
	 	$$ = $1;
	 	logfile<<"Line "<<line_count<<": simple_expression : term"<<endl<<endl<<$$->get_name()<<endl<<endl;
	 }
	| simple_expression ADDOP term {
	 	$$ = new SymbolInfo();
	 	$$->set_name($1->get_name()+$2->get_name()+$3->get_name());	 	
	 	logfile<<"Line "<<line_count<<": simple_expression : simple_expression ADDOP term"<<endl<<endl;
	 	if($3->get_type() == "VOID" || $1->get_type() == "VOID"){
			errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
			logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;			
		}	 	
	 	if($1->get_type() == "CONST_FLOAT" || $3->get_type() == "CONST_FLOAT"){$$->set_type("CONST_FLOAT");}
	 	else {$$->set_type("CONST_INT");}
	 	logfile<<$$->get_name()<<endl<<endl;
	 } 
	;
					
term :	unary_expression {
			$$ = new SymbolInfo();
			$$ = $1;
			logfile<<"Line "<<line_count<<": term : unary_expression"<<endl<<endl<<$$->get_name()<<endl<<endl;
		}
     |  term MULOP unary_expression {
			$$ = new SymbolInfo();
			//logfile<<$1->get_name()<<" "<<$1->get_type()<<" "<<$3->get_name()<<" "<<$3->get_type()<<endl;
			$$->set_name($1->get_name()+$2->get_name()+$3->get_name());			
			logfile<<"Line "<<line_count<<": term : term MULOP unary_expression"<<endl<<endl;
			if($2->get_name() == "%"){
				if($1->get_type() != "CONST_INT" || $3->get_type() != "CONST_INT"){
					errorfile<<"Error at line "<<line_count<<" : Non-Integer operand on modulus operator "<<endl<<endl; error_count++;
					logfile<<"Error at line "<<line_count<<" : Non-Integer operand on modulus operator "<<endl<<endl;
					$$->set_type("undefined");
				}
				else if($3->get_name() == "0"){
					errorfile<<"Error at line "<<line_count<<" : Modulus by Zero "<<endl<<endl; error_count++;
					logfile<<"Error at line "<<line_count<<" : Modulus by Zero"<<endl<<endl;
					$$->set_type("undefined");
				}
				else {$$->set_type("CONST_INT");}
			}
			else if($3->get_type() == "VOID" || $1->get_type() == "VOID"){
				errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
				logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;
				$$->set_type($1->get_type());
			}		
			else if($1->get_type() == "CONST_FLOAT" || $3->get_type() == "CONST_FLOAT"){
				$$->set_type("CONST_FLOAT");
			}	
			else {$$->set_type("CONST_INT");}
			logfile<<$$->get_name()<<endl<<endl;					
		}
     ;

unary_expression : ADDOP unary_expression {
    		$$ = new SymbolInfo();
		 	$$->set_name($1->get_name()+$2->get_name());
		 	$$->set_type($2->get_type());
		 	logfile<<"Line "<<line_count<<": unary_expression : ADDOP unary_expression"<<endl<<endl<<$$->get_name()<<endl<<endl;
		 }  
		 | NOT unary_expression {
    		$$ = new SymbolInfo();    		
		 	$$->set_name("!"+$2->get_name());
		 	$$->set_type($2->get_type());
		 	logfile<<"Line "<<line_count<<": unary_expression : NOT unary_expression"<<endl<<endl<<$$->get_name()<<endl<<endl;
		 }
		 | factor {
    		$$ = new SymbolInfo();    		
		 	$$ = $1;
		 	logfile<<"Line "<<line_count<<": unary_expression : factor"<<endl<<endl<<$$->get_name()<<endl<<endl;		 	
		 }
		 ;
	
factor	: variable {
			$$ = new SymbolInfo();
			$$ = $1;		 	
		 	logfile<<"Line "<<line_count<<": factor : variable"<<endl<<endl<<$$->get_name()<<endl<<endl;		
		}
	| id LPAREN argument_list RPAREN {
			$$ = new SymbolInfo();
		 	$$->set_name($1->get_name()+"("+$3->get_name()+")");		 		 	
		 	logfile<<"Line "<<line_count<<": factor : ID LPAREN argument_list RPAREN"<<endl<<endl;
		 	if(st->lookup($1->get_name()) != nullptr){
		 		si = st->lookup($1->get_name());
		 		$$->set_type(si->get_idtype());			 		
		 		//handling function call with non-function type identifier
		 		if(si->get_vartype() != "function"){
		 			logfile<<"Error at line "<<line_count<<" : Function call with non-function type identifier "<<$1->get_name()<<endl<<endl;
		 			errorfile<<"Error at line "<<line_count<<" : Function call with non-function type identifier "<<$1->get_name()<<endl<<endl; error_count++;
		 		}
		 		// handling function calls
		 		else{		 			
		 			int param = si->fp->param_no();
		 			char* str = new char[$3->get_type().length()+1];
					strcpy(str,$3->get_type().c_str());
					char* token = new char[$3->get_name().length()];
					token = strtok(str," ,");
					vector<string> vect;
					while(token != NULL){
						//cout<<line_count<<token<<endl;
						vect.push_back(token);						
						token = strtok(NULL," ,");
					}
					delete[] str;
					delete[] token;															
					if(vect.size() != param){
						//cout<<line_count<<" "<<vect.size()<<" "<<param<<endl;
						logfile<<"Error at line "<<line_count<<" : Total number of arguments mismatch in function call of function "<<$1->get_name()<<endl<<endl;
	 					errorfile<<"Error at line "<<line_count<<" : Total number of arguments mismatch in function call of function "<<$1->get_name()<<endl<<endl; error_count++;
					}
					else{
						for(int i=0;i<vect.size();i++){
							if(vect[i] != si->fp->param_list[i] && array_mismatch[mismatch_no] == false){							
								//cout<<line_count<<" "<<i<<vect[i]<<si->fp->param_list[i]<<endl;
								logfile<<"Error at line "<<line_count<<" : " <<i+1<<"th argument mismatch in function "<<$1->get_name()<<endl<<endl;
	 							errorfile<<"Error at line "<<line_count<<" : " <<i+1<<"th argument mismatch in function "<<$1->get_name()<<endl<<endl; error_count++;
	 							break;
							}
						}
						mismatch_no++;						
					}
		 		}
		 	}
		 	else{
		 		logfile<<"Error at line "<<line_count<<" : Undeclared function "<<$1->get_name()<<endl<<endl;
	 			errorfile<<"Error at line "<<line_count<<" : Undeclared function "<<$1->get_name()<<endl<<endl; error_count++;	 			
	 			$$->set_type("undeclared");
		 	}
		 	logfile<<$$->get_name()<<endl<<endl;		
		}
	| LPAREN expression RPAREN {
			$$ = new SymbolInfo();
		 	$$->set_name("("+$2->get_name()+")");
		 	$$->set_type($2->get_type());
		 	logfile<<"Line "<<line_count<<": factor : LPAREN expression RPAREN"<<endl<<endl<<$$->get_name()<<endl<<endl;		
		}
	| CONST_INT {
			$$ = new SymbolInfo();
			$$ = $1;						
			logfile<<"Line "<<line_count<<": factor : CONST_INT"<<endl<<endl<<$$->get_name()<<endl<<endl;
		}
	| CONST_FLOAT {
			$$ = new SymbolInfo();
			$$ = $1;			
			logfile<<"Line "<<line_count<<": factor : CONST_FLOAT"<<endl<<endl<<$$->get_name()<<endl<<endl;
		}
	| variable INCOP {
			$$ = new SymbolInfo();
		 	$$->set_name($1->get_name()+$2->get_name());
		 	$$->set_type($1->get_type());
		 	logfile<<"Line "<<line_count<<": factor : variable INCOP"<<endl<<endl<<$$->get_name()<<endl<<endl;		
		}
	| variable DECOP {
			$$ = new SymbolInfo();
		 	$$->set_name($1->get_name()+$2->get_name());
		 	$$->set_type($1->get_type());
		 	logfile<<"Line "<<line_count<<": factor : variable DECOP"<<endl<<endl<<$$->get_name()<<endl<<endl;		
		} 	
	;
	
argument_list : {            
            $$ = new SymbolInfo("", "ID");
            $$->set_idtype("nothing");            
            logfile<<"Line "<<line_count<<": argument_list: epsilon-production"<<endl<<endl;
            logfile<<""<<endl<< endl;  
	    }	  
		| arguments {
			$$ = new SymbolInfo();
		 	$$ = $1;
		 	logfile<<"Line "<<line_count<<": argument_list : arguments"<<endl<<endl<<$$->get_name()<<endl<<endl;		
		}
		;
	
arguments : arguments COMMA logic_expression {
			$$ = new SymbolInfo();
		 	$$->set_name($1->get_name()+","+$3->get_name());
		 	string type;
		 	//cout<<endl<<$3->get_name()<<$3->get_idtype()<<endl;
		 	if($1->get_type() == "ID" && $3->get_type() == "ID"){
		 		si = st->lookup($1->get_name());		 				 		
		 		SymbolInfo* sym = st->lookup($3->get_name());
		 		type = $1->get_idtype()+" "+sym->get_idtype();
		 		$$->set_type(type);
		 		//cout<<$$->get_type();	
		 	}
		 	else if($1->get_type() != "ID" && $3->get_type() != "ID"){
		 		$$->set_type($1->get_type()+" "+$3->get_type());
		 	}		 	
		 	logfile<<"Line "<<line_count<<": arguments : arguments COMMA logic_expression"<<endl<<endl<<$$->get_name()<<endl<<endl;		
		} 
	      | logic_expression {
			$$ = new SymbolInfo();
		 	$$ = $1;
		 	logfile<<"Line "<<line_count<<": arguments : logic_expression"<<endl<<endl<<$$->get_name()<<endl<<endl;		
		} 
	    ;

%%

int main(int argc,char *argv[])
{		
	if((fp=fopen(argv[1],"r"))==NULL)
	{
		printf("Cannot Open Input File.\n");
		exit(1);
	}	
	if((fp1 = fopen("log.txt","r")) == NULL)
	{
		printf("Cannot Open Output File.\n");
		exit(1);
	}
	if((fp2 = fopen("error.txt","r")) == NULL)
	{
		printf("Cannot Open Output File.\n");
		exit(1);
	}	
	yyin=fp;
	yyparse();	
	st->print_all(logfile);	
	logfile<<"Total lines : "<<line_count<<endl;
	logfile<<"Total errors : "<<error_count<<endl;	
	return 0;
}
