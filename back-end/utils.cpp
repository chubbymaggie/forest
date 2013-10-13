/*
 * =====================================================================================
 * /
 * |     Filename:  utils.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  10/12/2013 03:55:42 AM
 * |     Revision:  none
 * |     Compiler:  gcc
 * `-. .--------------------
 *    Y
 *    ,,  ,---,
 *   (_,\/_\_/_\     Author:   Pablo González de Aledo (), pablo.aledo@gmail.com
 *     \.\_/_\_/>    Company:  Universidad de Cantabria
 *     '-'   '-'
 * =====================================================================================
 */

#include "utils.h"

#define debug true

using namespace std;



int get_size(string type){

	if( type == "IntegerTyID32" )
		return 4;

	if( type == "DoubleTyID" )
		return 8;

	if( type == "FloatTyID" )
		return 8;

	if( type == "IntegerTyID8" )
		return 1;

	if( type == "IntegerTyID16" )
		return 2;

	if( type == "IntegerTyID64" )
		return 8;

	if( type == "int" )
		return 4;

	if( type == "PointerTyID")
		return 4;


	if( type.find(",") != string::npos ){
		int sum = 0;
		vector<string> tokens = tokenize(type,",");
		for( vector<string>::iterator it = tokens.begin(); it != tokens.end(); it++ ){
			sum += get_size(*it);
		}
		return sum;
	}


	printf("get_size type %s\n", type.c_str());

	assert(0 && "Unknown type");

}


int get_ini_elem(int nelem_target, string offset_tree){

	int depth = -1;
	int nelem = -1;
	for ( unsigned int i = 1; i < offset_tree.size(); i++) {
		if(offset_tree[i] == '(') depth++;
		if(offset_tree[i] == ')') depth--;
		if(depth == 0 && offset_tree[i] == '(' ){
			nelem++;
			//printf("elem %d at %d\n", nelem, i);
		}
		if(nelem == nelem_target){
			//printf("get_ini_elem %d %s : %d\n", nelem_target, offset_tree.c_str(), i);
			return i;

		}
	}

	assert(0 && "Unbalanced tree");

}

string close_str(string offset_tree){

	int depth = 0;
	for ( unsigned int i = 0; i < offset_tree.size(); i++) {
		if(offset_tree[i] == '(') depth++;
		if(offset_tree[i] == ')') depth--;
		if(depth == 0) return offset_tree.substr(0,i+1);
	}

	assert(0 && "Unbalanced tree");

}

string trimpar(string str){

	int n1 = str.find_first_not_of("()");
	int n2 = str.substr(n1).find_first_not_of("0123456789-");
	string firstnum = str.substr(n1).substr(0,n2);
	//printf("trimpar %s %s %d %d %s\n", str.c_str(), str.substr(n1).c_str(),  n1, n2, str.substr(n1).substr(0,n2).c_str() );
	assert( is_number(firstnum) && "ret is not a number");
	return firstnum;
}

bool has_index(string offset_tree, int index){

	int depth = -1;
	int nelem = -1;
	for ( unsigned int i = 1; i < offset_tree.size(); i++) {
		if(offset_tree[i] == '(') depth++;
		if(offset_tree[i] == ')') depth--;
		if(depth == 0 && offset_tree[i] == '(' ){
			nelem++;
		}
		if(nelem == index){
			return true;

		}
	}

	return false;
}






void myReplace(std::string& str, const std::string& oldStr, const std::string& newStr) {
	size_t pos = 0;
	while((pos = str.find(oldStr, pos)) != std::string::npos){
		str.replace(pos, oldStr.length(), newStr);
		pos += newStr.length();
	}
}


string itos(int i){
	stringstream i_ss;
	i_ss << i;
	return i_ss.str();
}

bool is_number(const std::string& s) {

	//printf("\e[33m is_number \e[0m %s\n", s.c_str() );

	if( s== "true" || s== "false") return true;

	if(s.substr(0,1) == "-") return is_number(s.substr(1));

	//printf("%s\n", s.substr(0,s.find(".")).c_str() );
	//printf("%s\n", s.substr(s.find(".")+1).c_str() );
	if( s.find(".") != string::npos ) return 
		is_number(s.substr(0,s.find("."))) &&
		is_number(s.substr(s.find(".")+1));


	if( s.find("e") != string::npos ) return 
		is_number(s.substr(0,s.find("e"))) &&
		is_number(s.substr(s.find("e")+1));

	std::string::const_iterator it = s.begin();
	while (it != s.end() && std::isdigit(*it)) ++it;
	return !s.empty() && it == s.end();
}


int count(string name, string character){

    int n = 0;
    string::size_type sz = 0;

    while ( (sz = name.find (character,sz) ) != string::npos  ){
        sz++; /*otherwise you start searching at your previous match*/
        n++;
    }
    return n;

}


int stoi(string str){
	int ret;
	sscanf(str.c_str(), "%d", &ret);
	return ret;
}
