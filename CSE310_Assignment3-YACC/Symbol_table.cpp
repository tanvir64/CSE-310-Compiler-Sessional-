#include<bits/stdc++.h>
using namespace std;

class FuncAttribute{
    string ret_type;
    string decl_type;

public:
    FuncAttribute(){}
    vector<string> param_list;
    vector<string> param_type;
    void set_rettype(string type){this->ret_type = type;}
    string get_rettype(){return ret_type;}
    void set_decltype(string decl_type){this->decl_type = decl_type;}
    string get_decltype(){return decl_type;}
    void add_param(string param){param_list.push_back(param);}
    int param_no(){return param_list.size();}
};

class SymbolInfo{
private:
    string name;
    string type;
    string idtype = "";
    string var_type;
public:
    FuncAttribute* fp;
    SymbolInfo(){}
    SymbolInfo(string name,string type)
    {
        this->name = name;
        this->type = type;
    }
    SymbolInfo* symbolInfo;
    void set_name(string name) {this->name = name;}
    void set_type(string type) {this->type = type;}
    void set_idtype(string idtype) {this->idtype = idtype;}
    void set_vartype(string var_type){this->var_type = var_type;}
    string get_name() {return name;}
    string get_type() {return type;}
    string get_idtype() {return idtype;}
    string get_vartype(){return var_type;}
};

class ScopeTable{
private:
    int num_buckets;
    int current_id;
    int position;
    string scope_id = "";
    vector<SymbolInfo*> *chain;
public:
    ScopeTable* parentScope = nullptr;
    string get_scopeid()
    {
        if(parentScope == nullptr){
            scope_id = to_string(get_id());
            return scope_id;
        }
        else{
            scope_id = parentScope->get_scopeid() + "." + to_string(get_id());
            return scope_id;
        }
    }
    void set_id(int id){current_id = id;}
    int get_id(){return current_id;}
    int Hash(string k){
        int sum = 0;
        for(int i=0;i<k.size();i++){
            sum += (int)k[i];
        }
        return (sum%num_buckets);
    }
    ScopeTable(int n){
        num_buckets = n;
        chain = new vector<SymbolInfo*>[num_buckets];
    }

    bool Insert(SymbolInfo* si)
    {
        int bucket_no;
        if(lookup(si->get_name()) == nullptr){
            bucket_no = Hash(si->get_name());
            chain[bucket_no].push_back(si);
            return true;
        }
        else
            return false;
    }

    SymbolInfo* lookup(string name)
    {
        int ind = Hash(name);
        for(int i=0;i<chain[ind].size();i++){
            if(chain[ind][i]->get_name() == name){
                return chain[ind][i];
            }
        }
        return nullptr;
    }

    bool delete_sym(string name)
    {
        if(lookup(name) != nullptr){
            int ind = Hash(name);
            for(int i=0;i<chain[ind].size();i++){
                if(chain[ind][i]->get_name() == name){
                    chain[ind].erase(chain[ind].begin()+i);
                    //cout<<"Deleted Entry "<<ind<<", "<<i<<" from current ScopeTable."<<endl;
                    //out<<"Deleted Entry "<<ind<<", "<<i<<" from current ScopeTable."<<endl;
                    return true;
                }
            }
        }
        return false;
    }

    void print_scope(ofstream& out)
    {
        out<<" ScopeTable # "<<get_scopeid()<<endl;
        for(int i=0;i<num_buckets;i++){
            if(chain[i].size() > 0){
                out<<"  "<<i<<" --> ";
                for(int j=0;j<chain[i].size();j++){
                    if(chain[i].size() > 0){
                        out<<"< "<<chain[i][j]->get_name()<<" , "<<chain[i][j]->get_type()<<"> ";
                    }
                }
                out<<endl;
            }
        }
        out<<endl;
    }

    ~ScopeTable()
    {
        chain[num_buckets].clear();
    }

};

class SymbolTable{
    int bucket_size;
    int scope_count = 0;
    ScopeTable **scopetable;
    int prev_level;
public:
    ScopeTable* curr_scope;
    SymbolTable(int n)
    {
        prev_level = 0;
        bucket_size = n;
        ScopeTable* sct = new ScopeTable(n);
        curr_scope = sct;
        scopetable = new ScopeTable*[1000];
        scopetable[scope_count++] = curr_scope;
        for(int i=0;i<scope_count;i++){
            if(curr_scope->parentScope == scopetable[i]->parentScope){
                prev_level += 1;
            }
        }
        curr_scope->set_id(prev_level);
    }

    void enter_scope(ofstream& out)
    {
        ScopeTable* sct = new ScopeTable(bucket_size);
        scopetable[scope_count++] = sct;
        sct->parentScope = curr_scope;
        curr_scope = sct;
        for(int i=0;i<scope_count;i++){
            if(curr_scope->parentScope == scopetable[i]->parentScope){
                prev_level += 1;
            }
        }
        curr_scope->set_id(prev_level);
        //cout<<"New ScopeTable with id "<<curr_scope->get_scopeid()<<" created."<<endl;
        //out<<" New ScopeTable with id "<<curr_scope->get_scopeid()<<" created."<<endl;
    }

    void exit_scope(ofstream& out)
    {
        ScopeTable* prev = curr_scope;
        curr_scope = prev->parentScope;
        //cout<<"ScopeTable with id "<<prev->get_scopeid()<<" removed."<<endl;
        //out<<" ScopeTable with id "<<prev->get_scopeid()<<" removed."<<endl;
    }

    bool insert_sym(SymbolInfo* si)
    {
        if(curr_scope->Insert(si)) return true;
        else return false;
    }

    SymbolInfo* lookup(string name)
    {
        ScopeTable* current = curr_scope;
        while(current != nullptr){
            SymbolInfo* sym = current->lookup(name);
            if(sym == nullptr) current = current->parentScope;
            else return sym;
        }
        return nullptr;
    }

    SymbolInfo* current_lookup(string name)
    {
        //cout<<curr_scope->get_id();
        return curr_scope->lookup(name);
    }

    bool remove_sym(string name)
    {
        bool deleted = curr_scope->delete_sym(name);
        if(deleted) return true;
        else return false;
    }

    void print_curr(ofstream& out)
    {
        curr_scope->print_scope(out);
    }

    void print_all(ofstream& out)
    {
        ScopeTable* current = curr_scope;
        while(current != nullptr){
            current->print_scope(out);
            //cout<<current->get_scopeid();
            current = current->parentScope;
        }
    }

};


