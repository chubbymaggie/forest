#include <cstdio>
#include <string>
#include <sstream>

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/FileManager.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Basic/TargetOptions.h"
#include "clang/Basic/TargetInfo.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Parse/ParseAST.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Rewrite/Frontend/Rewriters.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/raw_ostream.h"

using namespace clang;
using namespace std;


typedef struct Parsed_Function {
	string type_ret;
	SourceRange range;
} Parsed_Function;

vector<Parsed_Function> parsed_functions;
set<string> funcs_to_extract;

// By implementing RecursiveASTVisitor, we can specify which AST nodes
// we're interested in by overriding relevant methods.
class MyASTVisitor : public RecursiveASTVisitor<MyASTVisitor>
{
	public:
		MyASTVisitor(Rewriter &R)
			: TheRewriter(R)
		{}


		bool VisitFunctionDecl(FunctionDecl *f) {
			// Only function definitions (with bodies), not declarations.
			if (f->hasBody()) {


				// Function name
				DeclarationName DeclName = f->getNameInfo().getName();
				string FuncName = DeclName.getAsString();

				if( funcs_to_extract.find(FuncName) != funcs_to_extract.end() ){


					// Type name as string
					QualType QT = f->getResultType();
					string TypeStr = QT.getAsString();

					Parsed_Function parsed_function = { TypeStr, f->getSourceRange() };

					parsed_functions.push_back(parsed_function);

					TheRewriter.InsertText(f->getLocStart(), "");
				}

			}

			return true;
		}

	private:

		Rewriter &TheRewriter;
};


// Implementation of the ASTConsumer interface for reading an AST produced
// by the Clang parser.
class MyASTConsumer : public ASTConsumer
{
	public:
		MyASTConsumer(Rewriter &R)
			: Visitor(R)
		{}

		// Override the method that gets called for each parsed top-level
		// declaration.
		virtual bool HandleTopLevelDecl(DeclGroupRef DR) {
			for (DeclGroupRef::iterator b = DR.begin(), e = DR.end();
					b != e; ++b)
				// Traverse the declaration using our AST visitor.
				Visitor.TraverseDecl(*b);
			return true;
		}

	private:
		MyASTVisitor Visitor;
};


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
		command << "> /tmp/std_files";
		system(command.str().c_str());
	}

	{
		FILE *file = fopen ( "functions", "r" );
		char line [ 128 ]; // or other suitable maximum line size

		while ( fgets ( line, sizeof(line), file ) != NULL ){
			line[strlen(line)-1] = 0;
			funcs_to_extract.insert(string(line));
		}
		fclose ( file );
	}




	// CompilerInstance will hold the instance of the Clang compiler for us,
	// managing the various objects needed to run the compiler.
	CompilerInstance* TheCompInst = new CompilerInstance();
	//TheCompInst.createDiagnostics(0, 0);
	TheCompInst->createDiagnostics();

	// Initialize target info with the default triple for our platform.
	TargetOptions TO;
	TO.Triple = llvm::sys::getDefaultTargetTriple();
	TargetInfo *TI = TargetInfo::CreateTargetInfo(
			TheCompInst->getDiagnostics(), &TO);
	TheCompInst->setTarget(TI);

	TheCompInst->createFileManager();
	FileManager &FileMgr = TheCompInst->getFileManager();
	TheCompInst->createSourceManager(FileMgr);
	SourceManager &SourceMgr = TheCompInst->getSourceManager();
	TheCompInst->createPreprocessor();
	TheCompInst->createASTContext();

	// A Rewriter helps us manage the code rewriting task.
	Rewriter TheRewriter;
	TheRewriter.setSourceMgr(SourceMgr, TheCompInst->getLangOpts());

	// Set the main file handled by the source manager to the input file.
	const FileEntry *FileIn = FileMgr.getFile("/tmp/std_files");
	SourceMgr.createMainFileID(FileIn);
	TheCompInst->getDiagnosticClient().BeginSourceFile(
			TheCompInst->getLangOpts(),
			&(TheCompInst->getPreprocessor()));

	// Create an AST consumer instance which is going to get called by
	// ParseAST.
	MyASTConsumer TheConsumer(TheRewriter);

	// Parse the file to AST, registering our consumer as the AST consumer.
	ParseAST(TheCompInst->getPreprocessor(), &TheConsumer,
			TheCompInst->getASTContext());

	// At this point the rewriter's buffer should be full with the rewritten
	// file contents.
	const RewriteBuffer *RewriteBuf =
		TheRewriter.getRewriteBufferFor(SourceMgr.getMainFileID());

	unsigned int begin = parsed_functions[0].range.getBegin().getRawEncoding();
	unsigned int end   = parsed_functions[0].range.getEnd().getRawEncoding();
	string type = parsed_functions[0].type_ret;

	printf("%s %s\n", type.c_str(), string(RewriteBuf->begin(), RewriteBuf->end()).substr(begin+1, end-begin-1).c_str() );
	//llvm::outs() << string(RewriteBuf->begin(), RewriteBuf->end());

	return 0;
}
