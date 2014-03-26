#ifdef KLEE
#include "/llvm-2.9/klee/include/klee/klee.h"
#endif

int KernelMode  ;
int Executive  ;
int s  ;
int UNLOADED  ;
int NP  ;
int DC  ;
int SKIP1  ;
int SKIP2  ;
int MPR1  ;
int MPR3  ;
int IPC  ;
int pended  ;
int compFptr  ;
int compRegistered  ;
int lowerDriverReturn  ;
int setEventCalled  ;
int customIrp  ;
int myStatus  ;


int main() {
	int status ;
	int irp = 0;
	int pirp ;
	int pirp__IoStatus__Status ;
	int irp_choice = 0;
	int devobj = 0;
	int __cil_tmp8 ;
#ifdef KLEE
	klee_make_symbolic(&irp,sizeof(irp),"main_register_irp");
	klee_make_symbolic(&irp_choice,sizeof(irp_choice),"main_register_irp_choice");
#endif

	{
		{
			;
			KernelMode = 0 ;
			Executive  = 0;
			s  = 0;
			UNLOADED  = 0;
			NP  = 0;
			DC  = 0;
			SKIP1  = 0;
			SKIP2  = 0;
			MPR1  = 0;
			MPR3  = 0;
			IPC  = 0;
			pended  = 0;
			compFptr  = 0;
			compRegistered  = 0;
			lowerDriverReturn  = 0;
			setEventCalled  = 0;
			customIrp  = 0;
			myStatus  = 0;

			status = 0;
			pirp = irp;
			/*_BLAST_init();*/
		}
		if (status >= 0) {
			s = NP;
			customIrp = 0;
			setEventCalled = customIrp;
			lowerDriverReturn = setEventCalled;
			compRegistered = lowerDriverReturn;
			pended = compRegistered;
			pirp__IoStatus__Status = 0;
			myStatus = 0;
			if (irp_choice == 0) {
				pirp__IoStatus__Status = -1073741637;
				myStatus = -1073741637;
			}
			{
				/*stub_driver_init();*/
			}
			{
				if(status >= 0){
					__cil_tmp8 = 1;
				}
				else{
					__cil_tmp8 = 0;
				} 
				if (! __cil_tmp8) {
					return (-1);
				}
			}
			int tmp_ndt_1 = 0;
#ifdef KLEE
			klee_make_symbolic(&tmp_ndt_1,sizeof(tmp_ndt_1),"main_register_tmp_ndt_1");
#endif
			if (tmp_ndt_1 == 3) {
				goto switch_1_3;
			} else {
				goto switch_1_default;
				if (0) {
switch_1_3: 
					{
						/*status = KbFilter_PnP(devobj, pirp);*/
					}
					goto switch_1_break;
switch_1_default: ;
		  return (-1);
				} else {
switch_1_break: ;
				}
			}
		}
		if (pended == 1) {
			if (s == NP) {
				s = NP;
			} else {
				goto _L___2;
			}
		} else {
_L___2: 
			if (pended == 1) {
				if (s == MPR3) {
					s = MPR3;
				} else {
					goto _L___1;
				}
			} else {
_L___1: 
				if (s != UNLOADED) {
					if (status != -1) {
						if (s != SKIP2) {
							if (s != IPC) {
								if (s == DC) {
									goto _L___0;
								}
							} else {
								goto _L___0;
							}
						} else {
_L___0: 
							if (pended == 1) {
								if (status != 259) {
									{
										/*errorFn();*/
									}
								}
							} else {
								if (s == DC) {
									if (status == 259) {

									}
								} else {
									if (status != lowerDriverReturn) {

									}
								}
							}
						}
					}
				}
			}
		}

		return (status);
	}
}
