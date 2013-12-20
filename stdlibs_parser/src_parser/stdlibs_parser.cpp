#include <stdio.h>
#include <stdlib.h>
#include <vector>
#include <string>
#include <string.h>
#include <sstream>
#include <set>
#include <assert.h>

using namespace std;

vector<string> funcs_to_extract;
vector<string> structs_to_extract;

typedef struct Location{
	int row;
	int column;
} Location;

typedef struct Range {
	Location start;
	Location end;
} Range;


vector<Range> get_range_functions(){

	vector<Range> ret_v;

	for( vector<string>::iterator it = funcs_to_extract.begin(); it != funcs_to_extract.end(); it++ ){
		stringstream command;
		command << "cd /tmp/;";
		command << "cat ast | grep FunctionDecl | egrep '> \\<" << *it << "\\>' | grep -v '/usr/'";
		command << " > ast_filter";
		system(command.str().c_str());

		FILE *file = fopen ( "/tmp/ast_filter", "r" );
		char line [ 512 ]; /* or other suitable maximum line size */
		vector<string> lines;
		
		while ( fgets ( line, sizeof(line), file ) != NULL ){
			line[strlen(line)-1] = 0;
			lines.push_back(string(line));

		}
		fclose ( file );

		assert(lines.size() == 1);

		command.str("");
		

		FILE *fp;
		char ret[128];
		//command << "cat /tmp/ast_filter | sed 's/[^:]*:\([^:]*\):\([^,]*\),[^:]*:\([^:]*\):\([^>]*\)>.*/\1 \2 \3 \4/g'";
		command << "cat /tmp/ast_filter | sed 's/[^:]*:\\([^:]*\\):\\([^,]*\\),[^:]*:\\([^:]*\\):\\([^>]*\\)>.*/\\1 \\2 \\3 \\4/g'";
		
		int r1, c1, r2, c2;
		fp = popen(command.str().c_str(), "r");
		fscanf(fp, "%d %d %d %d", &r1, &c1, &r2, &c2);
		pclose(fp);

		//printf("%d %d %d %d\n", r1, c1, r2, c2);


		Location start = {r1, c1};
		Location end = {r2, c2};
		Range range = {start, end};
		ret_v.push_back(range);
		
		
	}

	return ret_v;
	
}


vector<Range> get_range_structs(){

	vector<Range> ret;

	for( vector<string>::iterator it = structs_to_extract.begin(); it != structs_to_extract.end(); it++ ){
		stringstream command;
		command << "cd /tmp/;";
		command << "cat ast | grep RecordDecl | egrep '> struct \\<" << *it << "\\>' | grep -v '/usr/'";
		command << " > ast_filter";
		system(command.str().c_str());

		FILE *file = fopen ( "/tmp/ast_filter", "r" );
		char line [ 512 ]; /* or other suitable maximum line size */
		vector<string> lines;
		
		while ( fgets ( line, sizeof(line), file ) != NULL ){
			line[strlen(line)-1] = 0;
			lines.push_back(string(line));

		}
		fclose ( file );

		assert(lines.size() == 1);

		command.str("");
		

		FILE *fp;
		char ret[128];
		//command << "cat /tmp/ast_filter | sed 's/[^:]*:\([^:]*\):\([^,]*\),[^:]*:\([^:]*\):\([^>]*\)>.*/\1 \2 \3 \4/g'";
		command << "cat /tmp/ast_filter | sed 's/[^:]*:\\([^:]*\\):\\([^,]*\\),[^:]*:\\([^:]*\\):\\([^>]*\\)>.*/\\1 \\2 \\3 \\4/g'";
		
		int r1, c1, r2, c2;
		fp = popen(command.str().c_str(), "r");
		fscanf(fp, "%d %d %d %d", &r1, &c1, &r2, &c2);
		pclose(fp);

		//printf("%d %d %d %d\n", r1, c1, r2, c2);
		
		
	}

	return ret;
	
}

void out_line(int count, string line_s, vector<Range> ranges){

	bool start = false;
	bool middle = false;
	bool end = false;
	int column;


	for( vector<Range>::iterator it = ranges.begin(); it != ranges.end(); it++ ){
		if( it->start.row == count ){ start = true; column = it->start.column; break; }
		else if( it->start.row < count && count < it->end.row ) { middle = true; break; }
		else if( it->end.row == count ) { end = true; column = it->end.column; break;}
	}

	//printf("out_line %d %d %d %d %d\n", count, start, middle, end, ranges.size());


	if(start) printf("%s\n", line_s.substr(column-1).c_str() );
	else if(middle) printf("%s\n", line_s.c_str() );
	else if(end) printf("%s\n\n", line_s.substr(0, column).c_str() );
	
}

void output_range(vector<Range> ranges){

	FILE *file = fopen ( "/tmp/std_files", "r" );
	char line [ 128 ]; /* or other suitable maximum line size */
	string line_s;

	int count = 0;
	
	while ( fgets ( line, sizeof(line), file ) != NULL ){
		line[strlen(line)-1] = 0;
		line_s = string(line);
		count++;


		out_line(count, line_s, ranges);


	}
	fclose ( file );
	

}


int main() {

	{
		FILE *file = fopen ( "files", "r" );
		char line [ 128 ]; // or other suitable maximum line size
		vector<string> files;

		while ( fgets ( line, sizeof(line), file ) != NULL ){
			line[strlen(line)-1] = 0;
			files.push_back(string(line));
		}
		fclose ( file );

		stringstream command;
		command << "cat";
		for( vector<string>::iterator it = files.begin(); it != files.end(); it++ ){
			command << " " << *it;
		}
		command << "> /tmp/std_files.c";
		system(command.str().c_str());

		command.str("");
		command << "cd /tmp/;";
		command << "clang -Xclang -ast-dump -fno-color-diagnostics std_files.c > ast 2>/dev/null";
		system(command.str().c_str());
	}

	{
		FILE *file = fopen ( "functions", "r" );
		char line [ 128 ]; // or other suitable maximum line size

		while ( fgets ( line, sizeof(line), file ) != NULL ){
			line[strlen(line)-1] = 0;
			funcs_to_extract.push_back(string(line));
		}
		fclose ( file );
	}

	{
		FILE *file = fopen ( "structs", "r" );
		char line [ 128 ]; // or other suitable maximum line size

		while ( fgets ( line, sizeof(line), file ) != NULL ){
			line[strlen(line)-1] = 0;
			structs_to_extract.push_back(string(line));
		}
		fclose ( file );
	}


	//printf("/* structures */\n\n");
	//vector<Range>  structs = get_range_structs();
	//output_range(structs);
	
	printf("/* functions */\n\n");
	vector<Range> functions = get_range_functions();
	output_range(functions);


	return 0;
}
