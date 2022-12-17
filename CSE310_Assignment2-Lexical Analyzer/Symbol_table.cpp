#include<bits/stdc++.h>
using namespace std;

class SymbolInfo{
private:
    string name;
    string type;
public:
    SymbolInfo(string name,string type)
    {
        this->name = name;
        this->type = type;
    }
    SymbolInfo* symbolInfo;
    ///void set_name(string name){symbol_name = name;}
    ///void set_type(string type){symbol_type = type;}
    string get_name(){return name;}
    string get_type(){return type;}
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
    bool Insert(string,string);
    SymbolInfo* lookup(string);
    bool delete_sym(string);
    void print_scope(ofstream&);
    ~ScopeTable();
};

bool ScopeTable::Insert(string name,string type)
{
    int bucket_no;
    if(lookup(name) == nullptr){
        SymbolInfo* si = new SymbolInfo(name,type);
        bucket_no = Hash(name);
        chain[bucket_no].push_back(si);
        return true;
    }
    else
        return false;
}

SymbolInfo* ScopeTable::lookup(string name)
{
    int ind = Hash(name);
    for(int i=0;i<chain[ind].size();i++){
        if(chain[ind][i]->get_name() == name){
            //cout<<"Found in ScopeTable# "<<get_scopeid()<<" at position "<<ind<<", "<<i<<endl;
            //out<<"Found in ScopeTable# "<<get_scopeid()<<" at position "<<ind<<", "<<i<<endl;
            return chain[ind][i];
        }
    }
    return nullptr;
}

bool ScopeTable::delete_sym(string name)
{
    if(lookup(name) != nullptr){
        int ind = Hash(name);
        for(int i=0;i<chain[ind].size();i++){
            if(chain[ind][i]->get_name() == name){
                chain[ind].erase(chain[ind].begin()+i);
                cout<<"Deleted Entry "<<ind<<", "<<i<<" from current ScopeTable."<<endl;
                //out<<"Deleted Entry "<<ind<<", "<<i<<" from current ScopeTable."<<endl;
                return true;
            }
        }
    }
    return false;
}

void ScopeTable::print_scope(ofstream& out)
{
    //cout<<"ScopeTable # "<<get_scopeid()<<endl;
    out<<"\nScopeTable # "<<get_scopeid()<<endl;
    for(int i=0;i<num_buckets;i++){
        if(chain[i].size() > 0){
            out<<" "<<i<<" --> ";
            for(int j=0;j<chain[i].size();j++){
                if(chain[i].size() > 0){
                    out<<"< "<<chain[i][j]->get_name()<<" : "<<chain[i][j]->get_type()<<"> ";
                }
            }
            out<<endl;
        }

    }
}

ScopeTable::~ScopeTable()
{
    chain[num_buckets].clear();
}

class SymbolTable{
    int bucket_size;
    int scope_count = 0;
    ScopeTable **scopetable;
    ScopeTable* curr_scope;
public:
    SymbolTable(int n)
    {
        int prev_level = 0;
        bucket_size = n;
        ScopeTable* sct = new ScopeTable(n);
        curr_scope = sct;
        scopetable = new ScopeTable*[100];
        scopetable[scope_count++] = curr_scope;
        for(int i=0;i<scope_count;i++){
            if(curr_scope->parentScope == scopetable[i]->parentScope){
                prev_level += 1;
            }
        }
        curr_scope->set_id(prev_level);
    }
    void enter_scope();
    void exit_scope();
    bool insert_sym(string,string,ofstream&);
    bool remove_sym(string);
    SymbolInfo* lookup(string);
    void print_curr(ofstream&);
    void print_all(ofstream&);
};

void SymbolTable::enter_scope()
{
    int prev_level = 0;
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
    //out<<"New ScopeTable with id "<<curr_scope->get_scopeid()<<" created."<<endl;
}

void SymbolTable::exit_scope()
{
    ScopeTable* prev = curr_scope;
    curr_scope = prev->parentScope;
    //cout<<"ScopeTable with id "<<prev->get_scopeid()<<" removed."<<endl;
    //out<<"ScopeTable with id "<<prev->get_scopeid()<<" removed."<<endl;
}

bool SymbolTable::insert_sym(string name,string type,ofstream& out)
{
    if(curr_scope->Insert(name,type)) return true;
    else {
        //out<<"\n"<<name<<" already exists in current ScopeTable"<<endl;
        return false;
    }
}

SymbolInfo* SymbolTable::lookup(string name)
{
    ScopeTable* current = curr_scope;
    while(current != nullptr){
        SymbolInfo* sym = current->lookup(name);
        if(sym == nullptr) current = current->parentScope;
        else return sym;
    }
    return nullptr;
}

bool SymbolTable::remove_sym(string name)
{
    bool deleted = curr_scope->delete_sym(name);
    if(deleted) return true;
    else return false;
}

void SymbolTable::print_curr(ofstream& out)
{
    curr_scope->print_scope(out);
}

void SymbolTable::print_all(ofstream& out)
{
    ScopeTable* current = curr_scope;
    while(current != nullptr){
        current->print_scope(out);
        //out<<endl;
        current = current->parentScope;
    }
}

