/*
 * =====================================================================================
 * /
 * |     Filename:  architecture.cpp
 * |
 * |  Description:  
 * |
 * |      Version:  1.0
 * |      Created:  04/15/2014 05:34:24 PM
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

using namespace std;

string hex_representation(int in, string type){
	char b[20];
	//printf("internal_representation_type %s\n", type.c_str());

	if(type == "IntegerTyID32")
		sprintf(b, "%08x", in);
	else if(type == "Int")
		sprintf(b, "%08x", in);
	else if(type == "bool")
		sprintf(b, "%08x", in);
	else if(type == "IntegerTyID16")
		sprintf(b, "%04x", in);
	else if(type == "IntegerTyID64")
		sprintf(b, "%08x", in);
	else if(type == "IntegerTyID8")
		sprintf(b, "%02x", in);
	else if(type == "PointerTyID")
		sprintf(b, "%016x", in);
	else if(type == "Pointer")
		sprintf(b, "%016x", in);
	else
		assert(0 && "Unknown type");

	//printf("internal representation in %s a %d b %s\n", in.c_str(), a, b);
	return "#x" + string(b);
}


int bits(string type){
	//printf("bits %s\n", type.c_str());
	if(type == "IntegerTyID32") return 32;
	else if(type == "IntegerTyID16") return 16;
	else if(type == "DoubleTyID") return 64;
	else if(type == "IntegerTyID64") return 64;
	else if(type == "IntegerTyID8" ) return 8;
	else if(type == "Int" ) return 32;
	else if(type == "PointerTyID" ) return 64;
	else if(type == "FloatTyID" ) return 32;
	else if(type == "Pointer" ) return 64;
	else if(type == "bool" ) return 8;
	else assert(0 && "Unknown type");

}


string internal_representation_int(int in, string type, string solver){

	char b[20];
	if( solver == "bitvector"){
		if(type == "IntegerTyID32"){
			sprintf(b, "#x%08x", (in < 0)?((1 << 32) + in):in);
		} else if (type == "IntegerTyID64"){
			sprintf(b, "#x%08x", (in < 0)?((1 << 64) + in):in);
		} else if (type == "IntegerTyID1"){
			sprintf(b, "#x%02x", (in < 0)?((1 << 8) + in):in);
		} else if (type == "IntegerTyID16"){
			sprintf(b, "#x%04x", (in < 0)?((1 << 16) + in):in);
		} else if (type == "IntegerTyID8"){
			sprintf(b, "#x%02x", (in < 0)?((1 << 8) + in):in);
		} else if (type == "Int"){
			sprintf(b, "#x%02x", (in < 0)?((1 << 32) + in):in);
		} else if(type == "PointerTyID"){
			sprintf(b, "#x%016x", (in < 0)?((1 << 64) + in):in);
		} else {
			cerr << "type " << type << endl;
			assert(0 && "Unknown type");
		}

	} else {
		sprintf(b, "%d", in);
	}

	return string(b);
}

string internal_representation_float(float in, string type, string solver){
	char b[20];

	if( solver == "bitvector")
		sprintf(b, "#x%02x", in);
	else
		sprintf(b, "%d", in);

	return string(b);
}


int primary_size( string type_str ){

	if( type_str == "IntegerTyID32" ) return 4;
	if( type_str == "IntegerTyID16" ) return 2;
	if( type_str == "IntegerTyID8" ) return 1;
	if( type_str == "IntegerTyID64" ) return 8;
	if( type_str == "PointerTyID" ) return 8; // <
	if( type_str == "FloatTyID" ) return 4;
	if( type_str == "DoubleTyID" ) return 8;

	cerr << type_str << endl;
	assert(0 && "Unknown type");

}


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
		return 8; // <


	if( type.find(',') != string::npos ){
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




