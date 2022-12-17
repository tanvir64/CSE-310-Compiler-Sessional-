%{
#include<bits/stdc++.h>
#include<algorithm>
#include<fstream>
#include<cstdlib>
#include<cstring>
#include<string>
#include "Symbol_table.cpp"

//#define YYSTYPE SymbolInfo*

///need to handle arrays for all expressions
using namespace std;

int yyparse(void);
int yylex(void);
//int yydebug = 1;
extern FILE *yyin;
extern int line_count;
extern int error_count;
extern int yylineno;
extern char* yytext;

//file pointers and symboltable object initinalized
SymbolInfo* si = nullptr;
SymbolTable* st = new SymbolTable(30);
FILE *fp,*fp1,*fp2,*fp3;
ofstream logfile("log.txt",ios::out);
ofstream errorfile("error.txt",ios::out);
ofstream code("code.asm",ios::out);
ofstream optimized("optimized_code.asm",ios::out);
// extra variables and functions
vector<string> params[100]; // keeps the parameters of a function
int vect_no=0,param_no = 0;
bool has_param[100] = {false};
bool array_mismatch[100] = {false}; // if variable and arrays are compared, it will be true
int mismatch_no = 0;
string func_name;
string type;
// for inserting the function name into the SymbolTable
bool pre_enter[100] = {false};
int pn = 0,pre_no = 0;
vector<string> has_decl; // keeps track of the functions that have been declared

// for generating assembly code
int label_count = 0;
int temp_count = 0;
vector<string> var_list;// for storing the variables deaclared in the source program
vector<string> arg_list;
vector<string> func_param[10];
int func_no = 0;
bool func_main = false;
unordered_multimap<string,string> find_scope;
unordered_map<string,int> find_func;

void yyerror(char *s){}

//function for generating new label for assembly code
string newLabel()
{
	string label = "L";
	stringstream ss;
	ss<<label_count;
	label += ss.str();
	label_count++;
	return label;
}
//function for generating new temporary varible for assembly code
string newTemp()
{
	string temp = "t";
	stringstream ss;
	ss<<temp_count;
	temp += ss.str();
	temp_count++;
	var_list.push_back("\t"+temp+"\tdw\t?");
	return temp;
}

void optimize_code(string assembly_code){
	//optimized<<assembly_code;
	string line;
	vector<string> line1_vect;
	vector<string> line2_vect;
	vector<string> line_vect;
	stringstream ss(assembly_code);
	while(getline(ss,line,'\n')){
		line_vect.push_back(line);
	}
	for(int i=0;i<line_vect.size();i++){	
		if(i != line_vect.size()-1){
			string ins1 = line_vect[i].substr(1,4);
			ins1.erase(remove(ins1.begin(),ins1.end(),' '),ins1.end());
			string ins2 = line_vect[i+1].substr(1,4);
			ins2.erase(remove(ins2.begin(),ins2.end(),' '),ins2.end());
			//cout<<ins1<<" "<<ins2;
			if(ins1 == "mov" &&  ins2 == "mov"){
				//cout<<"multi move!!";
				stringstream line1_stream(line_vect[i]);
				stringstream line2_stream(line_vect[i+1]);
				while(getline(line1_stream,line,' ')){
					line1_vect.push_back(line);
				}
				while(getline(line2_stream,line,' ')){
					line2_vect.push_back(line);
				}	
				//cout<<line1_vect[1].substr(0,line1_vect[1].length()-1)<<" "<<line2_vect[2].substr(0,line2_vect[2].length())<<endl;
				if((line1_vect[1].substr(0,line1_vect[1].length()-1) == line2_vect[2].substr(0,line2_vect[2].length())) && (line1_vect[2].substr(0,line1_vect[2].length()) == line2_vect[1].substr(0,line2_vect[1].length()-1))){
					optimized<<line_vect[i]<<endl;
					i++;
				}
				else{
					optimized<<line_vect[i]<<endl;
				}
				line1_vect.clear();
				line2_vect.clear();				
			}
			else{
				optimized<<line_vect[i]<<endl;
			}
		}
		else{
			optimized<<line_vect[i];
		}					
					
	}	
}

// whether a function has been declared or not
bool has_entry(string s){
	int found = 0;
	//cout<<"checking "<<s<<endl;				
	for(int i=0;i<has_decl.size();i++){
		if(has_decl[i] == s) {
			//cout<<"found "<<s<<endl;
			found = 1;
			break;
		}
	}
	if(found == 1) return true; 	
	else return false;
}
//finds the length of a function declaration
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

start : program {
		logfile<<"Line "<<line_count-1<<": start : program"<<endl<<endl;
		if(error_count == 0){						
			var_list.push_back("\tfunc_val\tdw\t?");			
			string final_assembly = ".model small \n.stack 100h\n.data\n";			
			for(int i=0;i<var_list.size();i++){
				final_assembly += var_list[i]+"\n";
			}			
			final_assembly += ".code\n";						
			string print_proc = "print_id proc\n";					
			print_proc += "\tpush ax\n\tpush bx\n\tpush cx\n\tpush dx\n";
			print_proc += "\tmov bx, ax\n";
			print_proc += "\tcmp bx, 0\n\tje out\n";
			print_proc += "\tjnl pos\n\tmov ah, 2\n";
			print_proc += "\tmov dl, '-'\n\tint 21h\n\tneg bx\n";
			//label pos
			print_proc += "pos"+(string)":\n";
			print_proc += "\tmov ax, bx\n";			
			print_proc += "\txor cx, cx\n";
			//label check			
			print_proc += "check"+(string)":\n";
			print_proc += "\tcmp ax, 0\n";
			print_proc += "\tje loop1\n";	
			print_proc += "\txor dx, dx\n";		
			print_proc += "\tmov bx,10\n";
			print_proc += "\tdiv bx\n";
			print_proc += "\tpush dx\n";
			print_proc += "\tinc cx\n";			
			print_proc += "\tjmp check\n";			
			//label loop1
			print_proc += "loop1"+(string)":\n";
			print_proc += "\tjcxz return\n";
			print_proc += "\tpop dx\n";
			print_proc += "\tadd dx, 030h\n";
			print_proc += "\tmov ah,2\n\tint 21h\n";			
			print_proc += "\tdec cx\n";
			print_proc += "\tjmp loop1\n";
			//label out
			print_proc += "out"+(string)":\n";
			print_proc += "\tmov ah, 2\n";
			print_proc += "\tmov dx, '0'\n";
			print_proc += "\tint 21h\n";						
			//label return
			print_proc += "return"+(string)":\n";
			print_proc += "\tmov ah, 2\n";
			print_proc += "\tmov dl, 0dh\n\tint 21h\n";
			print_proc += "\tmov ah, 2\n";
			print_proc += "\tmov dl, 0ah\n\tint 21h\n";
			print_proc += "\tpop dx\n\tpop cx\n\tpop bx\n\tpop ax\n";						
			print_proc += "\tret\n";
			print_proc += "print_id endp\n";
			
			final_assembly += print_proc;
			final_assembly += $1->get_code();
			code<<final_assembly;
			stringstream ss(final_assembly);
			string line,assembly = "";
			while(getline(ss,line,'\n')){
				if(line.substr(0,2) != "\t;")
					assembly += line+"\n";
			}
			optimize_code(assembly);
		}
		delete $1;		
	}	
	;

program : program unit  {			
			$$->set_name($1->get_name()+"\n"+$2->get_name());
			$$->set_code($1->get_code()+$2->get_code());
			logfile<<"\nLine "<<line_count<<": program : program unit"<<endl<<endl<<$$->get_name()<<endl<<endl;			
		}
	| unit {
		$$ = $1;
		$$->set_code($1->get_code());
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
			$$->set_code($1->get_code());
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
			//cout<<"pre enter "<<func_name<<" "<<si<<endl;
			if(func_name == "main"){func_main = true;}
			bool b = st->insert_sym(si);
			pre_enter[pre_no] = true;			
			pn = pre_no;						
			pre_no++;							
		}
		else{
			pre_enter[pre_no] = false;
			pn = pre_no++;
		}							
	}
	;
	     	 
func_declaration : type_specifier id pre_enter_func_name LPAREN parameter_list RPAREN SEMICOLON {
			$$ = new SymbolInfo();
			string emp = " ";			
			$$->set_name($1+emp+$2->get_name()+"("+$5->get_name()+");");			
			//cout<<$2->get_name();
			si = st->lookup($2->get_name());			
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
				//cout<<"in dec "<<$2->get_name()<<endl;				
				//cout<<si<<endl;								
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
			si = st->lookup($2->get_name());
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
			si = st->lookup($2->get_name());
			find_func.insert(make_pair($2->get_name(),func_no));

			string proc_name = $2->get_name();
			string new_code = "";				
			new_code += proc_name+" proc\n";
			new_code += "\tpush ax\n\tpush bx\n\tpush cx\n\tpush dx\n";			
			for(int i=0;i<func_param[func_no].size();i++){
				new_code += "\tpush "+func_param[func_no][i]+"\n";
			}	

			if(has_entry($2->get_name()) || (has_entry($2->get_name()) == false && pre_enter[pn] == false)){								
				//cout<<"in error detection "<<$2->get_name()<<" "<<si->fp->get_decltype()<<endl;											
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
			new_code += $7->get_code();
			new_code += proc_name+ " endp\n";			
			$$->set_code(new_code);
			func_no++; 
			logfile<<"Line "<<line_count<<": func_definition : type_specifier ID LPAREN parameter_list RPAREN compound_statement"<<endl<<endl<<$$->get_name()<<endl<<endl;		
		}
		| type_specifier id pre_enter_func_name LPAREN RPAREN compound_statement {
			$$ = new SymbolInfo();
			string emp = " ";
			$$->set_name($1+emp+$2->get_name()+"("+")"+$6->get_name());
			find_func.insert(make_pair($2->get_name(),func_no));
			
			string proc_name = $2->get_name();
			string new_code = "";						
			new_code += proc_name+" proc\n";			
			if($2->get_name() == "main"){				
				new_code += "\tmov ax, @data\n";
				new_code += "\tmov ds, ax\n";				
			}	
			else{
				new_code += "\tpush ax\n\tpush bx\n\tpush cx\n\tpush dx\n";
				for(int i=0;i<var_list.size();i++){
					new_code += "push "+var_list[i]+"\n";
				}
			}
			si = st->lookup($2->get_name());		
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
			new_code += $6->get_code();
			new_code += proc_name+ " endp\n";
			new_code += "end "+proc_name;
			$$->set_code(new_code);
			func_no++;
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
				var_list.push_back("\t"+$4->get_name()+"_"+st->curr_scope->get_scopeid()+"\tdw\t?");
				find_scope.insert(make_pair($4->get_name(),st->curr_scope->get_scopeid()));
		  		func_param[func_no].push_back($4->get_name()+"_"+st->curr_scope->get_scopeid());
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
			has_param[vect_no] = true;
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
				var_list.push_back("\t"+$2->get_name()+"_"+st->curr_scope->get_scopeid()+"\tdw\t?");
				find_scope.insert(make_pair($2->get_name(),st->curr_scope->get_scopeid()));
				func_param[func_no].push_back($2->get_name()+"_"+st->curr_scope->get_scopeid());
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
			has_param[vect_no] = true;
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

compound_statement : LCURL {if(params[vect_no].size() == 0 || pre_enter[pn] ==false) {st->enter_scope(logfile);}} statements RCURL{				
			$$ = new SymbolInfo();											
			$$->set_name("{\n"+$3->get_name()+"\n}");	
			int count = params[vect_no].size();							
			//for(int i=0;i<count;i++){cout<<params[vect_no][i];}				
			
			string new_code = $3->get_code();			
			$$->set_code(new_code);

			logfile<<"Line  "<<line_count<<": compound_statement : LCURL statements RCURL"<<endl<<endl<<$$->get_name()<<endl<<endl;													
			st->print_all(logfile);
			st->exit_scope(logfile);
			//if(count != 0 && pre_enter[pn] ==false) {st->exit_scope(logfile);}
			vect_no++;			
		}
	    | LCURL {if(params[vect_no].size() == 0 || pre_enter[pn] ==false) {st->enter_scope(logfile);}} RCURL {
			$$ = new SymbolInfo();
			string str($1);
			$$->set_name($1);
			$$->set_code("");							
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
				SymbolInfo* sym = st->current_lookup(token);															
				if(sym != nullptr){					
					//sym = st->current_lookup(token);										
					if(sym->get_idtype() == ""){
						if(strcmp(type,"int") == 0) {sym->set_idtype("CONST_INT");}
						else if(strcmp(type,"float") == 0) {sym->set_idtype("CONST_FLOAT");}
						else if(strcmp(type,"void") == 0) {
							errorfile<<"Error at line "<<line_count<<" : Variable type cannot be void"<<endl<<endl;error_count++;	 
		  					logfile<<"Error at line "<<line_count<<" : Variable type cannot be void"<<endl<<endl;
						}
					}
				}
				else if(st->lookup(token) != nullptr){					
					SymbolInfo* sym = st->lookup(token);											
					if(sym->get_idtype() == ""){
						if(strcmp(type,"int") == 0) {sym->set_idtype("CONST_INT");}
						else if(strcmp(type,"float") == 0) {sym->set_idtype("CONST_FLOAT");}
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
					logfile<<"Line "<<line_count<<": type_specifier : INT"<<endl<<endl<<$$<<endl<<endl; }
 		| FLOAT {
					$$ = "float";
					logfile<<"Line "<<line_count<<": type_specifier : FLOAT"<<endl<<endl<<$$<<endl<<endl; }
 		| VOID {
					$$ = "void";					
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
				var_list.push_back("\t"+$3->get_name()+"_"+st->curr_scope->get_scopeid()+"\tdw\t?");
				find_scope.insert(make_pair($3->get_name(),st->curr_scope->get_scopeid()));
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
				//cout<<$3->get_name()<<" "<<$3->get_vartype()<<endl;
				string array = "\t"+$3->get_name()+"_"+st->curr_scope->get_scopeid()+"\tdw\t"+$5->get_name()+"\tdup(?)";
				var_list.push_back(array);
				find_scope.insert(make_pair($3->get_name(),st->curr_scope->get_scopeid()));
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
				var_list.push_back("\t"+$1->get_name()+"_"+st->curr_scope->get_scopeid()+"\tdw\t?");
		  		find_scope.insert(make_pair($1->get_name(),st->curr_scope->get_scopeid()));
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
				string array = "\t"+$1->get_name()+"_"+st->curr_scope->get_scopeid()+"\tdw\t"+$3->get_name()+"\tdup(?)";
				var_list.push_back(array);
				find_scope.insert(make_pair($1->get_name(),st->curr_scope->get_scopeid()));
		  		bool b = st->insert_sym(id);
		  	}
			logfile<<"Line "<<line_count<<": declaration_list : ID LTHIRD CONST_INT RTHIRD"<<endl<<endl<<$$->get_name()<<endl<<endl;					  			  
		  }
 		  ;
 		  
statements : statements statement {
	 	$$ = new SymbolInfo();
	 	$$->set_name($1->get_name()+"\n"+$2->get_name());
	 	logfile<<"Line "<<line_count<<": statements : statements statement"<<endl<<endl<<$$->get_name()<<endl<<endl;
		string new_code = $1->get_code()+$2->get_code();
		$$->set_code(new_code);
		//code<<$$->get_code();	
		delete $2;	
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
		$$->set_code($1->get_code());
	 	logfile<<"Line "<<line_count<<": statement : expression_statement"<<endl<<endl<<$$->get_name()<<endl<<endl;
	 }
	  | compound_statement {
	 	$$ = new SymbolInfo();
	 	$$ = $1;
		$$->set_code($1->get_code());
	 	logfile<<"Line "<<line_count<<": statement : compound_statement"<<endl<<endl<<$$->get_name()<<endl<<endl;
	 }
	  | FOR LPAREN expression_statement expression_statement expression RPAREN statement {
	 	$$ = new SymbolInfo();	 	
	 	$$->set_name("for("+$3->get_name()+$4->get_name()+$5->get_name()+")"+$7->get_name());
	 	$$->set_type("for");
	 	
		//for assembly
		string new_code = $3->get_code();		
		string label1 = newLabel();
		string label2 = newLabel();
		new_code += label1+":\n";
		new_code += $4->get_code();
		new_code += "\tmov ax, "+$4->get_name()+"\n";
		new_code += "\tcmp ax, 0\n";
		new_code += "\tje "+label2+"\n";
		new_code += $7->get_code()+$5->get_code();
		new_code += "\tjmp "+label1+"\n";
		new_code += label2+":\n";		
		$$->set_code(new_code);
		logfile<<"Line "<<line_count<<": statement : FOR LPAREN expression_statement expression_statement expression RPAREN statement"<<endl<<endl<<$$->get_name()<<endl<<endl;		
	 }
	  | IF LPAREN expression RPAREN statement %prec LOWER_THAN_ELSE {
	 	$$ = new SymbolInfo();	 		 	
	 	$$->set_name("if("+$3->get_name()+")"+$5->get_name());
	 	$$->set_type("if_then");

		//for assembly
		string new_code = $3->get_code();		
		string label = newLabel(); //false label
		new_code += "\tmov ax, "+$3->get_name()+"\n";
		new_code += "\tcmp ax, 0\n";
		new_code += "\tje "+label+"\n";
		new_code += $5->get_code();
		new_code += label+":\n";
		
		$$->set_code(new_code);
	 	
		logfile<<"Line "<<line_count<<": statement : IF LPAREN expression RPAREN statement"<<endl<<endl<<$$->get_name()<<endl<<endl;
	 }
	  | IF LPAREN expression RPAREN statement ELSE statement {
	 	$$ = new SymbolInfo();
	 	$$->set_name("if("+$3->get_name()+")"+$5->get_name()+"else"+$7->get_name());
	 	$$->set_type("if_then_else");
		
		//for assembly
		string new_code = $3->get_code();		
		string label1 = newLabel(); //false label
		string label2 = newLabel(); //next label		

		new_code += "\tmov ax, "+$3->get_name()+"\n";
		new_code += "\tcmp ax, 0\n";
		new_code += "\tje "+label1+"\n";				
		new_code += $5->get_code();
		new_code +=	"\tjmp "+label2+"\n";
		new_code += label1+":\n";		
		new_code += $7->get_code();		
		new_code += label2+":\n";

		$$->set_code(new_code);
	 	logfile<<"Line "<<line_count<<": statement : IF LPAREN expression RPAREN statement ELSE statement"<<endl<<endl<<$$->get_name()<<endl<<endl;
	 }
	  | WHILE LPAREN  expression RPAREN statement {
	 	$$ = new SymbolInfo();
	 	$$->set_name("while("+$3->get_name()+")"+$5->get_name());
	 	$$->set_type("while");		 
	 	logfile<<"Line "<<line_count<<": statement : WHILE LPAREN expression RPAREN statement"<<endl<<endl<<$$->get_name()<<endl<<endl;

		//for assembly
		string new_code = "";		
		string label1 = newLabel(); //true label
		string label2 = newLabel(); //false label
		new_code += label1+":\n";
		new_code += $3->get_code();
		new_code += "\tmov ax, "+$3->get_name()+"\n";
		new_code += "\tcmp ax, 0\n";
		new_code += "\tje "+label2+"\n";
		new_code += $5->get_code();
		new_code += "\tjmp "+label1+"\n";
		new_code += label2+":\n";
		$$->set_code(new_code);
	 }
	  | PRINTLN LPAREN id RPAREN SEMICOLON {
	 	$$ = new SymbolInfo();
	 	$$->set_name("printf("+$3->get_name()+");");
	 	$$->set_type("print");
	 	logfile<<"Line "<<line_count<<": statement : PRINTLN LPAREN ID RPAREN SEMICOLON"<<endl<<endl;
	 	
		string new_code = "\t;Line "+to_string(line_count)+(string)": "+$$->get_name()+"\n"; 
		if(st->lookup($3->get_name()) == nullptr){
	 		errorfile<<"Error at line "<<line_count<<" : Undeclared variable "<< ($3->get_name())<<endl<<endl;error_count++;	
  			logfile<<"Error at line "<<line_count<<" : Undeclared variable "<< ($3->get_name())<<endl<<endl;  
	 	}		

	 	logfile<<$$->get_name()<<endl<<endl;
	 }
	  | RETURN expression SEMICOLON {
	 	$$ = new SymbolInfo();	 	
	 	$$->set_name($1);
	 	$$->set_type("ret");
	 	logfile<<"Line "<<line_count<<": statement : RETURN expression SEMICOLON"<<endl<<endl<<$$->get_name()<<endl<<endl;
		string new_code = $2->get_code();
		new_code += "\t;Line "+to_string(line_count)+(string)": "+$$->get_name()+"\n";
		if($2->get_type() == "ID"){
			auto it = find_scope.find($2->get_name());
			new_code += "\tmov ax, "+$2->get_name()+"_"+it->second+"\n";
		}
		else {new_code += "\tmov ax, "+$2->get_name()+"\n";}
		new_code += "\tmov func_val, ax\n";
		for(int i=func_param[func_no].size()-1;i>=0;i--){
			new_code += "\tpop "+func_param[func_no][i]+"\n";
		}
		if(!func_main){
			new_code += "\tpop dx\n\tpop cx\n\tpop bx\n\tpop ax\n";
			new_code += "\tret\n";
		}			
		$$->set_code(new_code);
	 }
	;
	  
expression_statement : SEMICOLON {
	 	$$ = new SymbolInfo();
	 	$$->set_name("");
		$$->set_code(""); 		 	
	 } 			
	 | expression SEMICOLON {
	 	$$ = new SymbolInfo();
	 	//$$->set_name($1->get_name()+";");
		$$->set_name($1->get_name());
		$$->set_code($1->get_code());
	 	logfile<<"Line "<<line_count<<": expression_statement : expression SEMICOLON"<<endl<<endl<<$$->get_name()<<endl<<endl;
	 } 
	 ;
	  
variable : id {
	 	$$ = new SymbolInfo();	 	
	 	$$->set_name($1->get_name());
	 	SymbolInfo* sp = st->lookup($1->get_name());
	 	if(sp == nullptr){
  			errorfile<<"Error at line "<<line_count<<" : Undeclared variable "<< ($1->get_name())<<endl<<endl;error_count++;	
  			logfile<<"Error at line "<<line_count<<" : Undeclared variable "<< ($1->get_name())<<endl<<endl;  				  		
  		}  		
  		else{
  			$$ = $1;  			
  			logfile<<"Line "<<line_count<<": variable : ID"<<endl<<endl;
  			string str($1->get_name());
  			if(sp->get_vartype() == "array" && str.length() == 1 ){
  				array_mismatch[mismatch_no] = true;
  				errorfile<<"Error at line "<<line_count<<" : Type Mismatch, "<<$1->get_name()<<" is an array"<<endl<<endl; error_count++;
				logfile<<"Error at line "<<line_count<<" : Type Mismatch, "<<$1->get_name()<<" is an array"<<endl<<endl;
  			}
	  		$$->set_type(sp->get_type());
			$$->set_idtype(sp->get_idtype());
	  		$$->set_vartype(sp->get_vartype());
			$$->set_code("");
  		}	  		
	 	logfile<<$$->get_name()<<endl<<endl;
	 }		
	 | id LTHIRD expression RTHIRD {
	 	$$ = new SymbolInfo();
	 	$$->set_name($1->get_name()+"["+$3->get_name()+"]");
	 	string new_code = $3->get_code();
		SymbolInfo* sp = st->lookup($1->get_name());
	 	if(sp == nullptr){
  			errorfile<<"Error at line "<<line_count<<" : Undeclared variable "<< ($1->get_name())<<endl<<endl;error_count++;	
  			logfile<<"Error at line "<<line_count<<" : Undeclared variable "<< ($1->get_name())<<endl<<endl;
  			 		
  		}
	 	else{	 		
	 		$$->set_type(sp->get_idtype());		 			 	
		 	//$$->set_idtype(sp->get_idtype());	
		 	$$->set_vartype(sp->get_vartype()); 			 	
		 	logfile<<"Line "<<line_count<<": variable : ID LTHIRD expression RTHIRD"<<endl<<endl;
		 	if(sp->get_vartype() != "array"){
		 		errorfile<<"Error at line "<<line_count<<" : "<<$1->get_name()<<" not an array"<<endl<<endl;error_count++;
		 		logfile<<"Error at line "<<line_count<<" : "<<$1->get_name()<<" not an array"<<endl<<endl;
		 	}
		 	else if($3->get_type() != "CONST_INT"){
		 		errorfile<<"Error at line "<<line_count<<" : Expression inside third brackets not an integer"<<endl<<endl;error_count++;
		 		logfile<<"Error at line "<<line_count<<" :Expression inside third brackets not an integer"<<endl<<endl;
		 	}
			 	
	 	}
		new_code += "\tmov bx, "+$3->get_name()+"\n";
		new_code += "\tadd bx, bx\n";
		$$->set_code(new_code);		
		delete $3;
	 	logfile<<$$->get_name()<<endl<<endl; 
	 } 
	 ;
	 
expression : logic_expression {
	 	$$ = new SymbolInfo();
	 	$$ = $1;
		$$->set_code($1->get_code());
	 	logfile<<"Line  "<<line_count<<": expression : logic_expression"<<endl<<endl<<$$->get_name()<<endl<<endl;
	 }
	   | variable ASSIGNOP logic_expression {
	 	$$ = new SymbolInfo();
	 	//cout<<"line"<<line_count<<" "<<$3->get_name()<<" "<<$3->get_type()<<endl;	 	
	 	$$->set_name($1->get_name()+$2->get_name()+$3->get_name());		
	 	logfile<<"Line "<<line_count<<": expression : variable ASSIGNOP logic_expression"<<endl<<endl;
		
		string str = $1->get_name();
		//cout<<str;
		string token = "";
		int pos = str.find("[");
		if(pos != -1){
			for(int i=0;i<pos;i++){
				token += str[i];
			}
		}		
		else {token = $1->get_name();}		
	 	//for assembly
		string new_code = "\t;Line "+to_string(line_count)+(string)": "+$$->get_name()+"\n";
		new_code += $3->get_code()+$1->get_code();
		new_code += "\tmov ax, "+$3->get_name()+"\n";
		logfile<<$3->get_type();
		if(st->lookup(token) != nullptr){	 		
	 		si = st->lookup(token);	 		
	 		//logfile<<token<<" "<<si->get_idtype()<<endl;
		 	string var_type = si->get_idtype();
		 	//cout<<"line"<<line_count<<" "<<$1->get_name()<<" "<<var_type<<endl;
		 	if($3->get_type() == "VOID"){
				errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
				logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;
				$$->set_type($1->get_type());
			}			
		 	else if($3->get_type() != "undefined"){
		 		si = st->lookup(token);						 		
		 		if($3->get_type() != "undeclared"){
		 			if((var_type == "CONST_FLOAT" && ($3->get_type() == "CONST_INT" || $3->get_type() == "CONST_FLOAT" || ($3->get_type()== "ID" && ($3->get_idtype() == "CONST_INT" || $3->get_idtype() == "CONST_FLOAT"))))  || (var_type == "CONST_INT" && $3->get_type() == "CONST_INT" ) || (var_type == "CONST_INT" && $3->get_type() == "ID" && $3->get_idtype() == "CONST_INT" )){
		 				if(si->get_vartype() != "array"){
							auto it = find_scope.find(token);
							new_code += "\tmov "+token+"_"+it->second+", ax\n";
							//logfile<<new_code;
						}
						else{	
							auto it = find_scope.find(token);						
							new_code += "\tmov "+token+"_"+it->second+"[bx], ax\n";
						}
		 			}
		 			else if($3->get_type() != "ID" && var_type == "CONST_INT" && var_type != $3->get_type()){
			 			cout<<line_count<<":"<<var_type<<"->"<<$3->get_type()<<endl;			 	
				 		errorfile<<"Error at line "<<line_count<<" : Type Mismatch "<<endl<<endl;
				 		logfile<<"Error at line "<<line_count<<" : Type Mismatch "<<endl<<endl;
				 		error_count++;
				 	}
					else if($3->get_type() == "ID" && var_type == "CONST_INT" && var_type != $3->get_idtype()){
			 			cout<<line_count<<":"<<var_type<<"->"<<$3->get_idtype()<<endl;			 	
				 		errorfile<<"Error at line "<<line_count<<" : Type Mismatch "<<endl<<endl;
				 		logfile<<"Error at line "<<line_count<<" : Type Mismatch "<<endl<<endl;
				 		error_count++;
				 	}
					
			 	}			 	
			 	$$->set_type($1->get_type());
		 	}	 		
	 	}
		$$->set_code(new_code);
		delete $3;	 		 		 		 	
	 	logfile<<$$->get_name()<<endl<<endl;
	 }	
	   ;
			
logic_expression : rel_expression {
	 	$$ = new SymbolInfo();
	 	$$ = $1;
		$$->set_code($1->get_code());
	 	logfile<<"Line "<<line_count<<": logic_expression : rel_expression"<<endl<<endl<<$$->get_name()<<endl<<endl;
	 }
	 | rel_expression LOGICOP rel_expression {
	 	$$ = new SymbolInfo();
	 	$$->set_name($1->get_name()+$2->get_name()+$3->get_name());
	 	logfile<<"Line "<<line_count<<": logic_expression : LOGICOP rel_expression"<<endl<<endl;
		
		//for assembly
		string new_code = "\t;Line "+to_string(line_count)+(string)": "+$$->get_name()+"\n";
		new_code += $1->get_code()+$3->get_code();
		string label1 = newLabel();	//false label
		string label2 = newLabel(); //true label
		string temp = newTemp();

		if($3->get_type() == "VOID" && $1->get_type() != "VOID"){
			errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
			logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;			
			$$->set_type($1->get_type());
		}	 	
		else if($3->get_type() != "VOID" && $1->get_type() == "VOID"){
			errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
			logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;			
			$$->set_type($3->get_type());
		}
		else if($3->get_type() == "VOID" && $1->get_type() == "VOID"){
			errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
			logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;			
			$$->set_type("VOID");
		}
		else{
			if($2->get_name() == "&&"){				
				if($1->get_type() == "ID"){
					if($1->get_name().length() == 1){
						auto it = find_scope.find($1->get_name());
						new_code += "\tcmp "+$1->get_name()+"_"+it->second+", 0\n";
						new_code += "\tje "+label1+"\n";
					}
					else{ 
						string s = $1->get_name().substr(0,$1->get_name().length()-3);
						auto it = find_scope.find(s);						
						new_code += "\tcmp "+$1->get_name()+", 0\n";
						new_code += "\tje "+label1+"\n";
					}						
				}
				else{
					new_code += "\tcmp "+$1->get_name()+", 0\n";
					new_code += "\tje "+label1+"\n";
				}											
				if($3->get_type() == "ID"){
					if($3->get_name().length() == 1){
						auto it = find_scope.find($3->get_name());
						new_code += "\tcmp "+$3->get_name()+"_"+it->second+", 0\n";
						new_code += "\tje "+label1+"\n";
					}															
					else{ 
						string s = $3->get_name().substr(0,$3->get_name().length()-3);
						auto it = find_scope.find(s);						
						new_code += "\tcmp "+$3->get_name()+", 0\n";
						new_code += "\tje "+label1+"\n";
					}				
				}
				else{
					new_code += "\tcmp "+$3->get_name()+", 0\n";
					new_code += "\tje "+label1+"\n";
				}
				new_code += "\tmov "+temp+", 1\n";
				new_code += "\tjmp "+label2+"\n";
				new_code += label1+":\n";
				new_code += "\tmov "+temp+", 0\n";
				new_code += label2+":\n";
				$$->set_name(temp);				
			}
			else if($2->get_name() == "||"){
				if($1->get_type() == "ID"){
					if($1->get_name().length() == 1){
						auto it = find_scope.find($1->get_name());
						new_code += "\tcmp "+$1->get_name()+"_"+it->second+", 0\n";
						new_code += "\tje "+label1+"\n";
					}						
					else{ 
						string s = $1->get_name().substr(0,$1->get_name().length()-3);
						auto it = find_scope.find(s);						
						new_code += "\tcmp "+$1->get_name()+", 0\n";
						new_code += "\tje "+label1+"\n";
					}
				}
				else{
					new_code += "\tcmp "+$1->get_name()+", 0\n";
					new_code += "\tje "+label1+"\n";
				}
				if($3->get_type() == "ID"){
					if($3->get_name().length() == 1){
						auto it = find_scope.find($3->get_name());
						new_code += "\tcmp "+$3->get_name()+"_"+it->second+", 0\n";
						new_code += "\tje "+label1+"\n";
					}	
					else{ 
						string s = $3->get_name().substr(0,$3->get_name().length()-3);
						auto it = find_scope.find(s);						
						new_code += "\tcmp "+$3->get_name()+", 0\n";
						new_code += "\tje "+label1+"\n";
					}
				}
				else{
					new_code += "\tcmp "+$3->get_name()+", 0\n";
					new_code += "\tje "+label1+"\n";
				}
			}
			if(($1->get_type() == "CONST_INT" || $1->get_type() == "CONST_FLOAT") && ($3->get_type() == "CONST_INT" || $3->get_type() == "CONST_FLOAT")) {
				$$->set_type("CONST_INT");
			}	
		}
		$$->set_code(new_code);
		delete $3;	 		 	
	 	logfile<<$$->get_name()<<endl<<endl; 
	 }
	;
			
rel_expression : simple_expression { 
	 	$$ = new SymbolInfo();
	 	$$ = $1;
		$$->set_code($1->get_code());
	 	//cout<<$1->get_name()<<$1->get_type()<<endl;
	 	logfile<<"Line "<<line_count<<": rel_expression : simple_expression"<<endl<<endl<<$$->get_name()<<endl<<endl;
	 }		
	| simple_expression RELOP simple_expression {
	 	$$ = new SymbolInfo();
	 	$$->set_name($1->get_name()+$2->get_name()+$3->get_name());
	 	logfile<<"Line "<<line_count<<": rel_expression : simple_expression RELOP simple_expression"<<endl<<endl;
		//for assembly
		string new_code = "\t;Line "+to_string(line_count)+(string)": "+$$->get_name()+"\n";
		new_code += $1->get_code()+$3->get_code();				
		string temp = newTemp();
		string label1 = newLabel(); //false label
		string label2 = newLabel(); //true label				
	 	if($3->get_type() == "VOID" && $1->get_type() != "VOID"){
			errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
			logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;			
			$$->set_type($1->get_type());
		}	 	
		else if($3->get_type() != "VOID" && $1->get_type() == "VOID"){
			errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
			logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;			
			$$->set_type($3->get_type());
		}
		else if($3->get_type() == "VOID" && $1->get_type() == "VOID"){
			errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
			logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;			
			$$->set_type("VOID");
		}
		else{
			if($1->get_type() == "ID"){
				if($1->get_name().length() == 1){
					auto it = find_scope.find($1->get_name());
					new_code += "\tmov ax, "+$1->get_name()+"_"+it->second+"\n";
				}
				else{ 
					string s = $1->get_name().substr(0,$1->get_name().length()-3);
					auto it = find_scope.find(s);					
					new_code += "\tmov ax, "+s+"_"+it->second+"[bx]\n";
				}
			}
			else{
				new_code += "\tmov ax, "+$1->get_name()+"\n";
			}
			if($3->get_type() == "ID"){
				if($3->get_name().length() == 1){
					auto it = find_scope.find($3->get_name());
					new_code += "\tcmp ax, "+$3->get_name()+"_"+it->second+"\n";
				}
				else{ 
					string s = $1->get_name().substr(0,$3->get_name().length()-3);
					auto it = find_scope.find(s);					
					new_code += "\tcmp ax, "+s+"_"+it->second+"[bx]\n";
				}				
			}
			else{
				new_code += "\tcmp ax, "+$3->get_name()+"\n";
			}
			if($2->get_name()=="<"){
				new_code += "\tjge "+label1+"\n";	//jump to false label			
			}
			else if($2->get_name()=="<="){
				new_code += "\tjg "+label1+"\n";	//jump to false label			
			} 
			else if($2->get_name()==">"){
				new_code += "\tjle "+label1+"\n";	//jump to false label			
			}
			else if($2->get_name()==">="){
				new_code += "\tjl "+label1+"\n";	//jump to false label			
			}
			else if($2->get_name()=="=="){
				new_code += "\tjne "+label1+"\n";	//jump to false label			
			}
			if(($1->get_type() == "CONST_INT" || $1->get_type() == "CONST_FLOAT") && ($1->get_type() == "CONST_INT" || $1->get_type() == "CONST_FLOAT"))
				{$$->set_type("CONST_INT");
				//$$->set_idtype("CONST_INT");				
			}				 	
		}
		$$ = $1;
		logfile<<$$->get_name()<<endl<<endl;
		new_code += "\tmov "+temp+", 1\n";
		new_code += "\tjmp "+label2+"\n";
		new_code += label1+":\n\tmov "+temp+", 0\n";
		new_code += label2+":\n";
		$$->set_code(new_code);
		$$->set_name(temp);
		delete $3;	 	
	 } 	
	;
				
simple_expression : term {
	 	$$ = new SymbolInfo();
	 	$$ = $1;
		$$->set_code($1->get_code());		
	 	logfile<<"Line "<<line_count<<": simple_expression : term"<<endl<<endl<<$$->get_name()<<endl<<endl;
	 }
	| simple_expression ADDOP term {
		$$ = new SymbolInfo();
	 	$$->set_name($1->get_name()+$2->get_name()+$3->get_name());	 	
	 	logfile<<"Line "<<line_count<<": simple_expression : simple_expression ADDOP term"<<endl<<endl;

		//for assembly
		string new_code = "";
		new_code += $1->get_code()+$3->get_code();
		string temp = newTemp();		

		if($2->get_name() == "+"){
			if($3->get_type() == "VOID" && $1->get_type() != "VOID"){
				errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
				logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;			
				$$->set_type($1->get_type());
			}	 	
			else if($3->get_type() != "VOID" && $1->get_type() == "VOID"){
				errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
				logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;			
				$$->set_type($3->get_type());
			}
			else if($3->get_type() == "VOID" && $1->get_type() == "VOID"){
				errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
				logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;			
				$$->set_type("VOID");
			}
			else{
				if($1->get_type() == "CONST_FLOAT" || $3->get_type() == "CONST_FLOAT"){$$->set_type("CONST_FLOAT");}
				else if(($1->get_type() == "ID" && $1->get_idtype() == "CONST_FLOAT") || ($3->get_type() == "ID" && $3->get_idtype() == "CONST_FLOAT")){$$->set_type("CONST_FLOAT");}
				else {$$->set_type("CONST_INT");}
				if($1->get_name().length() == 1 && $1->get_type() == "ID"){
					auto it = find_scope.find($1->get_name());
					new_code += "\tmov ax, "+$1->get_name()+"_"+it->second+"\n";
				} 
				else{
					new_code += "\tmov ax, "+$1->get_name()+"\n";
				}
				if($3->get_name().length() == 1 && $3->get_type() == "ID"){
					auto it = find_scope.find($3->get_name());
					new_code += "\tadd ax, "+$3->get_name()+"_"+it->second+"\n";
				} 
				else{
					new_code += "\tadd ax, "+$3->get_name()+"\n";
				}
				new_code += "\tmov "+temp+", ax\n";
			}
		}
		else{
			if($3->get_type() == "VOID" && $1->get_type() != "VOID"){
				errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
				logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;			
				$$->set_type($1->get_type());
			}	 	
			else if($3->get_type() != "VOID" && $1->get_type() == "VOID"){
				errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
				logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;			
				$$->set_type($3->get_type());
			}
			else if($3->get_type() == "VOID" && $1->get_type() == "VOID"){
				errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
				logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;			
				$$->set_type("VOID");
			}	 	
			else{				
				if($1->get_type() == "CONST_FLOAT" || $3->get_type() == "CONST_FLOAT"){$$->set_type("CONST_FLOAT");}
				else if(($1->get_type() == "ID" && $1->get_idtype() == "CONST_FLOAT") || ($3->get_type() == "ID" && $3->get_idtype() == "CONST_FLOAT")){$$->set_type("CONST_FLOAT");}
				else {$$->set_type("CONST_INT");}
				if($1->get_name().length() == 1 && $1->get_type() == "ID"){
					auto it = find_scope.find($1->get_name());
					new_code += "\tmov ax, "+$1->get_name()+"_"+it->second+"\n";
				} 
				else{
					new_code += "\tmov ax, "+$1->get_name()+"\n";
				}
				if($3->get_name().length() == 1 && $3->get_type() == "ID"){
					auto it = find_scope.find($3->get_name());
					new_code += "\tsub ax, "+$3->get_name()+"_"+it->second+"\n";
				} 
				else{
					new_code += "\tsub ax, "+$3->get_name()+"\n";
				}
				new_code += "\tmov "+temp+", ax\n";
			}
		}			
		$$->set_name(temp);			
		$$->set_code(new_code); 				
		delete $3;
	 	logfile<<$$->get_name()<<endl<<endl;
	 } 
	;
					
term :	unary_expression {
			$$ = new SymbolInfo();
			$$ = $1;
			$$->set_code($1->get_code());
			logfile<<"Line "<<line_count<<": term : unary_expression"<<endl<<endl<<$$->get_name()<<endl<<endl;
		}
     |  term MULOP unary_expression {
			$$ = new SymbolInfo();
			$$->set_name($1->get_name()+$2->get_name()+$3->get_name());
			logfile<<"Line "<<line_count<<": term : term MULOP unary_expression"<<endl<<endl;

			//for assembly
			string new_code = "";
			new_code += "\t;Line "+to_string(line_count)+(string)": "+$$->get_name()+"\n";
			string temp = newTemp();
			new_code += $1->get_code()+$3->get_code();

			if($1->get_name().length() == 1 && $1->get_type() == "ID"){
				auto it = find_scope.find($1->get_name());
				new_code += "\tmov ax, "+$1->get_name()+"_"+it->second+"\n";
			} 
			else{
				new_code += "\tmov ax, "+$1->get_name()+"\n";
			}
			if($3->get_name().length() == 1 && $3->get_type() == "ID"){
				auto it = find_scope.find($3->get_name());
				new_code += "\tmov bx, "+$3->get_name()+"_"+it->second+"\n";
			} 
			else{
				new_code += "\tmov bx, "+$3->get_name()+"\n";
			}						
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
				else {
					if($3->get_type() == "VOID" && $1->get_type() != "VOID"){
						errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
						logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;			
						$$->set_type($1->get_type());
					}	 	
					else if($3->get_type() != "VOID" && $1->get_type() == "VOID"){
						errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
						logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;			
						$$->set_type($3->get_type());
					}
					else if($3->get_type() == "VOID" && $1->get_type() == "VOID"){
						errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
						logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;			
						$$->set_type("VOID");
					}
					else{
						$$->set_type("CONST_INT");
						new_code += "\txor dx,dx\n";
						new_code += "\tdiv bx\n";
						new_code += "\tmov "+ string(temp) + ", dx\n";
					}
				}
			}
			else if($2->get_name() == "*"){				
				if($3->get_type() == "VOID" && $1->get_type() != "VOID"){
					errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
					logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;			
					$$->set_type($1->get_type());
				}	 	
				else if($3->get_type() != "VOID" && $1->get_type() == "VOID"){
					errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
					logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;			
					$$->set_type($3->get_type());
				}
				else if($3->get_type() == "VOID" && $1->get_type() == "VOID"){
					errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
					logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;			
					$$->set_type("VOID");
				}
				else{
					if($1->get_type() == "CONST_FLOAT" || $3->get_type() =="CONST_FLOAT"){
						$$->set_type("CONST_FLOAT");
					}
					else {$$->set_type("CONST_INT");}
					new_code += "\tmul bx\n";
					new_code += "\tmov "+temp+", ax\n";
				}
			}					
			else {				
				if($3->get_type() == "VOID" && $1->get_type() != "VOID"){
					errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
					logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;			
					$$->set_type($1->get_type());
				}	 	
				else if($3->get_type() != "VOID" && $1->get_type() == "VOID"){
					errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
					logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;			
					$$->set_type($3->get_type());
				}
				else if($3->get_type() == "VOID" && $1->get_type() == "VOID"){
					errorfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl; error_count++;
					logfile<<"Error at line "<<line_count<<" : Void function used in expression "<<endl<<endl;			
					$$->set_type("VOID");
				}
				else if($3->get_name() == "0"){
					errorfile<<"Error at line "<<line_count<<" : Modulus by Zero "<<endl<<endl; error_count++;
					logfile<<"Error at line "<<line_count<<" : Modulus by Zero"<<endl<<endl;
					$$->set_type("undefined");
				}
				else{
					if($1->get_type() =="CONST_FLOAT" || $3->get_type() =="CONST_FLOAT" ){
						$$->set_type("CONST_FLOAT");
					}						
					else {$$->set_type("CONST_INT");}
					new_code += "\txor dx,dx\n";
					new_code += "\tdiv bx\n";
					new_code += "\tmov "+ string(temp) + ", ax\n";
				}
							
			}
			$$ = $1;
			logfile<<$$->get_name()<<endl<<endl;
			$$->set_name(temp);
			$$->set_code(new_code); 				
			delete $3;																											
		}
     ;

unary_expression : ADDOP unary_expression {
    		$$ = new SymbolInfo();
			$$ = $2;
		 	// $$->set_name($1->get_name()+$2->get_name());
		 	// $$->set_type($2->get_type());
			string new_code = "\t;Line "+to_string(line_count)+(string)": "+$1->get_name()+$2->get_name()+"\n";
			string temp = newTemp();			
			cout<<$2->get_vartype();		
			
			if($2->get_vartype() != "array"){
				if($1->get_name() == "-"){						
					auto it = find_scope.find($2->get_name());
					new_code += "\tmov ax, "+$2->get_name()+"_"+it->second+"\n";
					new_code += "\tneg ax\n";
					new_code += "\tmov "+temp+", ax\n";
					$$->set_code(new_code);
					$$->set_name(temp);
					//cout<<new_code<<endl;
				}				
			}
			else{
				new_code += $2->get_code();
				new_code += "\tmov ax, "+$2->get_name()+"\n";
				new_code += "\tneg ax\n";
				new_code += "\tmov "+temp+", ax\n";				
				$$->set_code(new_code);
				$$->set_name(temp);
			}						
		 	logfile<<"Line "<<line_count<<": unary_expression : ADDOP unary_expression"<<endl<<endl<<$$->get_name()<<endl<<endl;
		 }  
		 | NOT unary_expression {
    		$$ = new SymbolInfo();			
			$$ = $2;
			$$->set_name("!"+$2->get_name());
			string new_code = "\t;Line "+to_string(line_count)+(string)": "+$$->get_name()+"\n";
			new_code += $2->get_code();
			string temp = newTemp();
			//cout<<$2->get_name()<<$$->get_vartype();
			if($2->get_vartype() != "array"){
				auto it = find_scope.find($2->get_name());
				//cout<<it->first<<it->second;
				new_code += "\tmov ax, "+$2->get_name()+"_"+it->second+"\n";
				new_code += "\tnot ax\n";
				new_code += "\tmov "+temp+", ax\n";
			}
			else{
				new_code += "\tmov ax, "+$2->get_name()+"\n";
				new_code += "\tnot ax\n";
				new_code += "\tmov "+temp+", ax\n";
			}									
			$$->set_code(new_code);
			$$->set_name(temp);
		 	logfile<<"Line "<<line_count<<": unary_expression : NOT unary_expression"<<endl<<endl<<$$->get_name()<<endl<<endl;
		 }
		 | factor {
    		$$ = new SymbolInfo();    		
		 	$$ = $1;
			$$->set_code($1->get_code());
		 	logfile<<"Line "<<line_count<<": unary_expression : factor"<<endl<<endl<<$$->get_name()<<endl<<endl;		 	
		 }
		 ;
	
factor	: variable {
			$$ = new SymbolInfo();
			$$ = $1;		 	
		 	logfile<<"Line "<<line_count<<": factor : variable"<<endl<<endl<<$$->get_name()<<endl<<endl;
			
			string new_code = $1->get_code();
			if($1->get_name().length() == 1){
				$$->set_code(new_code);
			}
			else{
				string temp = newTemp();
				string s = $1->get_name().substr(0,1);
				auto it = find_scope.find(s);
				new_code += "\tmov ax, "+s+"_"+it->second+"[bx]\n";
				new_code += "\tmov "+temp+", ax\n";				
				$$->set_code(new_code);
				$$->set_name(temp);				
			}
																
		}
	| id LPAREN argument_list RPAREN {
			$$ = new SymbolInfo();
		 	$$->set_name($1->get_name()+"("+$3->get_name()+")");		 		 	
		 	logfile<<"Line "<<line_count<<": factor : ID LPAREN argument_list RPAREN"<<endl<<endl;		 	
			string new_code = $3->get_code(); 
			string temp = newTemp();			
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
					//no.of params mismatch
					//cout<<$1->get_name()<<" "<<func_no<<endl;														
					if(func_param[func_no-1].size() != param){
						cout<<line_count<<" "<<func_param[func_no-1].size()<<" "<<param<<endl;
						logfile<<"Error at line "<<line_count<<" : Total number of arguments mismatch in function call of function "<<$1->get_name()<<endl<<endl;
	 					errorfile<<"Error at line "<<line_count<<" : Total number of arguments mismatch in function call of function "<<$1->get_name()<<endl<<endl; error_count++;
					}
					//type of params mismatch
					else{
						for(int i=0;i<vect.size();i++){
							if(vect[i] != si->fp->param_list[i] && array_mismatch[mismatch_no] == false){							
								cout<<line_count<<" "<<i<<" "<<vect[i]<<" "<<si->fp->param_list[i]<<endl;
								logfile<<"Error at line "<<line_count<<" : " <<i+1<<"th argument mismatch in function "<<$1->get_name()<<endl<<endl;
	 							errorfile<<"Error at line "<<line_count<<" : " <<i+1<<"th argument mismatch in function "<<$1->get_name()<<endl<<endl; error_count++;
	 							break;
							}
						}
						mismatch_no++;						
					}									
					auto it = find_func.find($1->get_name());	
					int p = arg_list.size();
					//cout<<it->second<<" "<<p<<endl; 
					if(p == 1){
						new_code += "\tmov ax, "+arg_list[p-1]+"\n";
						new_code += "\tmov "+func_param[it->second][p-1]+", ax\n";
						new_code += "\tcall "+$1->get_name()+"\n";
						new_code += "\tmov ax, func_val\n";
						new_code += "\tmov "+temp+", ax\n";
					}
					else if(p == 2){
						//cout<<arg_list[p-2]<<" "<<arg_list[p-1];
						new_code += "\tmov ax, "+arg_list[p-2]+"\n";
						new_code += "\tmov "+func_param[it->second][p-2]+", ax\n";
						new_code += "\tmov bx, "+arg_list[p-1]+"\n";
						new_code += "\tmov "+func_param[it->second][p-1]+", bx\n";
						new_code += "\tcall "+$1->get_name()+"\n";
						new_code += "\tmov ax, func_val\n";
						new_code += "\tmov "+temp+", ax\n";
					}
					else if(p == 3){
						//cout<<arg_list[p-2]<<" "<<arg_list[p-1];
						new_code += "\tmov ax, "+arg_list[p-3]+"\n";
						new_code += "\tmov "+func_param[it->second][p-3]+", ax\n";
						new_code += "\tmov bx, "+arg_list[p-2]+"\n";
						new_code += "\tmov "+func_param[it->second][p-2]+", bx\n";
						new_code += "\tmov cx, "+arg_list[p-1]+"\n";
						new_code += "\tmov "+func_param[it->second][p-1]+", cx\n";
						new_code += "\tcall "+$1->get_name()+"\n";
						new_code += "\tmov ax, func_val\n";
						new_code += "\tmov "+temp+", ax\n";
					}
		 		}
		 	}
		 	else{
				if($1->get_name() != "println" ){
					logfile<<"Error at line "<<line_count<<" : Undeclared function "<<$1->get_name()<<endl<<endl;
					errorfile<<"Error at line "<<line_count<<" : Undeclared function "<<$1->get_name()<<endl<<endl; error_count++;	 			
					$$->set_type("undeclared");
				}
				else{
					if($3->get_vartype() != "array"){	
						auto it = find_scope.find($3->get_name());					
						new_code += "\tmov ax, "+$3->get_name()+"_"+it->second+"\n";						
						new_code += "\tcall print_id\n";
						$$->set_code(new_code);
					}
					else{
						new_code += "\tmov ax, "+$3->get_name()+"\n";
						new_code += "\tcall print_id\n";
						$$->set_code(new_code);
					}
				}
		 		
		 	}
			arg_list.clear();						
		 	logfile<<$$->get_name()<<endl<<endl;
			$$->set_name(temp);
			$$->set_code(new_code);		
		}
	| LPAREN expression RPAREN {
			$$ = new SymbolInfo();
		 	//$$->set_name("("+$2->get_name()+")");
			$$->set_name($2->get_name());
		 	$$->set_type($2->get_type());
			$$->set_code($2->get_code());
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
			
			char* str = new char[$1->get_name().length()+1];
			strcpy(str,$1->get_name().c_str());									
			char* token = new char[$1->get_name().length()];
			token = strtok(str,"[] ");
			vector<string> var;
			while(token != NULL){
				var.push_back(token);
				token = strtok(NULL,"[] ");
			}

			string variable,index;
			if(var.size() == 1) variable = var[0];			
			else{
				variable = var[0];
				index = var[1];
			}
			string new_code = "\t;Line "+to_string(line_count)+(string)": "+$$->get_name()+"\n";
			new_code += $1->get_code();			
			
			if(st->lookup(variable) != nullptr){
				si = st->lookup(variable);
				string temp = newTemp();
				if(si->get_vartype() != "array"){
					//assembly code for increment operation	
					auto it = find_scope.find(variable);				
					new_code += "\tmov ax, "+variable+"_"+it->second+"\n";
					new_code += "\tmov "+temp+", ax\n";
					new_code += "\tinc "+variable+"_"+it->second+"\n";					
					$$->set_code(new_code);					
				}
				else{	
					auto it = find_scope.find(variable);				
					new_code += "\tmov ax, "+variable+"_"+it->second+"[bx]\n";
					new_code += "\tmov "+temp+", ax\n";
					new_code += "\tinc "+variable+"_"+it->second+"[bx]\n";
					$$->set_code(new_code);				
				}
				$$->set_name(temp);
			}
		}
	| variable DECOP {
			$$ = new SymbolInfo();
		 	$$->set_name($1->get_name()+$2->get_name());
		 	$$->set_type($1->get_type());
			string new_code = "\t;Line "+to_string(line_count)+(string)": "+$$->get_name()+"\n";
			new_code += $1->get_code(); 
		 	logfile<<"Line "<<line_count<<": factor : variable DECOP"<<endl<<endl<<$$->get_name()<<endl<<endl;		
			
			char* str = new char[$1->get_name().length()+1];
			strcpy(str,$1->get_name().c_str());									
			char* token = new char[$1->get_name().length()];
			token = strtok(str,"[] ");
			vector<string> var;
			while(token != NULL){
				var.push_back(token);
				token = strtok(NULL,"[] ");
			}

			string variable,index;
			if(var.size() == 1) variable = var[0];			
			else{
				variable = var[0];
				index = var[1];
			}			
			if(st->lookup(variable) != nullptr){
				si = st->lookup(variable);
				string temp = newTemp();
				if(si->get_vartype() != "array"){
					//assembly code for decrement operation
					auto it = find_scope.find(variable);
					new_code += "\tmov ax, "+variable+"_"+it->second+"\n";
					new_code += "\tmov "+temp+", ax\n";
					new_code += "\tdec "+variable+"_"+it->second+"\n";
					$$->set_code(new_code);					
				}
				else{
					auto it = find_scope.find(variable);
					new_code += "\tmov ax, "+variable+"_"+it->second+"\n";
					new_code += "\tmov "+temp+", ax\n";
					new_code += "\tdec "+variable+"_"+it->second+"[bx]\n";
					$$->set_code(new_code);					
				}
				$$->set_name(temp);
			}
		} 	
	;
	
argument_list : {            
            $$ = new SymbolInfo("", "ID");
            $$->set_idtype("nothing");                        
	    }	  
		| arguments {
			$$ = new SymbolInfo();
		 	$$ = $1;
			$$->set_code($1->get_code());			 
		 	logfile<<"Line "<<line_count<<": argument_list : arguments"<<endl<<endl<<$$->get_name()<<endl<<endl;		
		}
		;
	
arguments : arguments COMMA logic_expression {
			$$ = new SymbolInfo();
		 	$$->set_name($1->get_name()+","+$3->get_name());
		 	string type;
			string new_code = $1->get_code()+$3->get_code();
		 	//cout<<endl<<$3->get_name()<<$3->get_idtype()<<endl;
			arg_list.push_back($3->get_name()+"_"+st->curr_scope->get_scopeid());
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
			$$->set_code($1->get_code());
			//cout<<$1->get_idtype();
			$$->set_type($1->get_idtype());
			arg_list.push_back($1->get_name()+"_"+st->curr_scope->get_scopeid());
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
	logfile.close();
	errorfile.close();
	code.close();
	optimized.close();
	logfile<<"Total lines : "<<line_count<<endl;
	logfile<<"Total errors : "<<error_count<<endl;	
	return 0;
}
