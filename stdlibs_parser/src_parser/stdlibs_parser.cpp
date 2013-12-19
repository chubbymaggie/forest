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

	vector<Range> ret;

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

		printf("%d %d %d %d\n", r1, c1, r2, c2);
		
		
	}

	return ret;
	
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

	vector<Range> functions = get_range_functions();



	return 0;
}
