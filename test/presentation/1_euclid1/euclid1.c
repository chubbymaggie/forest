
int main() {
	int a = 1, b = 1;

	if( a == 0 || b == 0 ) return 0;

	while(true){
		a = a%b;
		if(a==0){
			return b;
		}
		b = b%a;
		if(b==0){
			return a;
		}
	}
}
