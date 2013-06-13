int main(int argc, char** argv) {
	int b = argc + 3;

	if ( b < 5 ){
		if( b > 3 )
			return 2;
		return 1;
	} else {
		if( b < 7 )
			return 4;
		return 3;
	}
} 

