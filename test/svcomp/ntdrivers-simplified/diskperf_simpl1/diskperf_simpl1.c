

#ifdef KLEE
#include "/llvm-2.9/klee/include/klee/klee.h"
#endif


void IofCompleteRequest(int Irp , int PriorityBoost );
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
int routine  ;
int pirp  ;
int Executive ;
int KernelMode ;




void stub_driver_init(void) ;
void stubMoreProcessingRequired(void) ;
int main() ;
void errorFn(void) ;
void _BLAST_init(void) ;
int PoCallDriver(int DeviceObject , int Irp ) ;
int KeWaitForSingleObject(int Object , int WaitReason , int WaitMode , int Alertable , int Timeout ) ;
int KeSetEvent(int Event , int Increment , int Wait ) ;
void IofCompleteRequest(int Irp , int PriorityBoost ) ;
int IofCallDriver(int DeviceObject , int Irp ) ;
int IoBuildDeviceIoControlRequest(int IoControlCode , int DeviceObject , int InputBuffer , int InputBufferLength , int OutputBuffer , int OutputBufferLength , int InternalDeviceIoControl , int Event , int IoStatusBlock ) ;
void DiskPerfUnload(int DriverObject ) ;
void DiskPerfSyncFilterWithTarget(int FilterDevice , int TargetDevice ) ;
int DiskPerfStartDevice(int DeviceObject , int Irp ) ;
int DiskPerfShutdownFlush(int DeviceObject , int Irp ) ;
int DiskPerfSendToNextDriver(int DeviceObject , int Irp ) ;
int DiskPerfRemoveDevice(int DeviceObject , int Irp ) ;
int DiskPerfRegisterDevice(int DeviceObject ) ;
int DiskPerfIrpCompletion(int DeviceObject , int Irp , int Context ) ;
int DiskPerfIoCompletion(int DeviceObject , int Irp , int Context ) ;
int DiskPerfForwardIrpSynchronous(int DeviceObject , int Irp ) ;
int DiskPerfDispatchPower(int DeviceObject , int Irp ) ;
int DiskPerfDispatchPnp(int DeviceObject , int Irp ) ;
int DiskPerfDeviceControl(int DeviceObject , int Irp ) ;




void errorFn(void) 
{ 

  {
  goto ERROR;
  ERROR: 
#line 58
  return;
}
}
#line 61 "diskperf_simpl1.cil.c"
void _BLAST_init(void) 
{ 

  {
#line 65
  UNLOADED = 0;
#line 66
  NP = 1;
#line 67
  DC = 2;
#line 68
  SKIP1 = 3;
#line 69
  SKIP2 = 4;
#line 70
  MPR1 = 5;
#line 71
  MPR3 = 6;
#line 72
  IPC = 7;
#line 73
  s = UNLOADED;
#line 74
  pended = 0;
#line 75
  compFptr = 0;
#line 76
  compRegistered = 0;
#line 77
  lowerDriverReturn = 0;
#line 78
  setEventCalled = 0;
#line 79
  customIrp = 0;
#line 80
  return;
}
}
#line 83 "diskperf_simpl1.cil.c"
void DiskPerfSyncFilterWithTarget(int FilterDevice , int TargetDevice ) 
{ int FilterDevice__Flags ;
  int TargetDevice__Characteristics ;
  int FilterDevice__Characteristics ;
  int propFlags ;

  {
#line 90
  //propFlags = 0;
#line 91
  //FilterDevice__Flags |= propFlags;
#line 92
  //propFlags = TargetDevice__Characteristics & 7;
#line 93
  //FilterDevice__Characteristics |= propFlags;
#line 94
  return;
}
}
#line 97 "diskperf_simpl1.cil.c"
int DiskPerfDispatchPnp(int DeviceObject , int Irp ) 
{ int Irp__Tail__Overlay__CurrentStackLocation;
  int irpSp__MinorFunction;
  int irpSp ;
  int status ;
  int tmp ;
#ifdef KLEE
  klee_make_symbolic(&Irp__Tail__Overlay__CurrentStackLocation,sizeof(Irp__Tail__Overlay__CurrentStackLocation),"Irp__Tail__Overlay__CurrentStackLocation");
  klee_make_symbolic(&irpSp__MinorFunction,sizeof(irpSp__MinorFunction),"irpSp__MinorFunction");
#endif

  {
#line 105
  irpSp = Irp__Tail__Overlay__CurrentStackLocation;
#line 106
  if (irpSp__MinorFunction == 0) {
    goto switch_0_0;
  } else {
#line 109
    if (irpSp__MinorFunction == 2) {
      goto switch_0_2;
    } else {
      goto switch_0_default;
#line 114
      if (0) {
        switch_0_0: 
        {
#line 117
        status = DiskPerfStartDevice(DeviceObject, Irp);
        }
        goto switch_0_break;
        switch_0_2: 
        {
#line 122
        status = DiskPerfRemoveDevice(DeviceObject, Irp);
        }
        goto switch_0_break;
        switch_0_default: 
        {
#line 127
        tmp = DiskPerfSendToNextDriver(DeviceObject, Irp);
        }
#line 129
        return (tmp);
      } else {
        switch_0_break: ;
      }
    }
  }
#line 136
  return (status);
}
}
#line 139 "diskperf_simpl1.cil.c"
int DiskPerfIrpCompletion(int DeviceObject , int Irp , int Context ) 
{ int Event ;

  {
  {
#line 144
  Event = Context;
#line 145
  KeSetEvent(Event, 0, 0);
  }
#line 147
  return (-1073741802);
}
}
#line 150 "diskperf_simpl1.cil.c"
int DiskPerfStartDevice(int DeviceObject , int Irp ) 
{ int DeviceObject__DeviceExtension;
  int deviceExtension__TargetDeviceObject;
  int Irp__IoStatus__Status ;
  int deviceExtension ;
  int status ;
#ifdef KLEE
  klee_make_symbolic(&DeviceObject__DeviceExtension,sizeof(DeviceObject__DeviceExtension),"DeviceObject__DeviceExtension");
  klee_make_symbolic(&deviceExtension__TargetDeviceObject,sizeof(deviceExtension__TargetDeviceObject),"deviceExtension__TargetDeviceObject");
#endif

  {
  {
#line 159
  deviceExtension = DeviceObject__DeviceExtension;
#line 160
  status = DiskPerfForwardIrpSynchronous(DeviceObject, Irp);
#line 161
  DiskPerfSyncFilterWithTarget(DeviceObject, deviceExtension__TargetDeviceObject);
#line 162
  DiskPerfRegisterDevice(DeviceObject);
#line 163
  Irp__IoStatus__Status = status;
#line 164
  myStatus = status;
#line 165
  IofCompleteRequest(Irp, 0);
  }
#line 167
  return (status);
}
}
#line 170 "diskperf_simpl1.cil.c"
int DiskPerfRemoveDevice(int DeviceObject , int Irp ) 
{ int DeviceObject__DeviceExtension;
  int deviceExtension__WmilibContext;
  int Irp__IoStatus__Status ;
  int status ;
  int deviceExtension ;
  int wmilibContext ;

#ifdef KLEE
  klee_make_symbolic(&DeviceObject__DeviceExtension,sizeof(DeviceObject__DeviceExtension),"DeviceObject__DeviceExtension");
  klee_make_symbolic(&deviceExtension__WmilibContext,sizeof(deviceExtension__WmilibContext),"deviceExtension__WmilibContext");
#endif

  {
  {
#line 180
  deviceExtension = DeviceObject__DeviceExtension;
#line 181
  wmilibContext = deviceExtension__WmilibContext;
#line 182
  status = DiskPerfForwardIrpSynchronous(DeviceObject, Irp);
#line 183
  Irp__IoStatus__Status = status;
#line 184
  myStatus = status;
#line 185
  IofCompleteRequest(Irp, 0);
  }
#line 187
  return (status);
}
}
#line 190 "diskperf_simpl1.cil.c"
int DiskPerfSendToNextDriver(int DeviceObject , int Irp ) 
{ int Irp__CurrentLocation;
  int Irp__Tail__Overlay__CurrentStackLocation;
  int DeviceObject__DeviceExtension;
  int deviceExtension__TargetDeviceObject;
  int deviceExtension ;
  int tmp ;

#ifdef KLEE
  klee_make_symbolic(&Irp__CurrentLocation,sizeof(Irp__CurrentLocation),"Irp__CurrentLocation");
  klee_make_symbolic(&Irp__Tail__Overlay__CurrentStackLocation,sizeof(Irp__Tail__Overlay__CurrentStackLocation),"Irp__Tail__Overlay__CurrentStackLocation");
  klee_make_symbolic(&DeviceObject__DeviceExtension,sizeof(DeviceObject__DeviceExtension),"DeviceObject__DeviceExtension");
  klee_make_symbolic(&deviceExtension__TargetDeviceObject,sizeof(deviceExtension__TargetDeviceObject),"deviceExtension__TargetDeviceObject");
#endif

  {
#line 199
  if (s == NP) {
#line 200
    s = SKIP1;
  } else {
    {
#line 203
    errorFn();
    }
  }
  {
#line 207
  Irp__CurrentLocation ++;
#line 208
  Irp__Tail__Overlay__CurrentStackLocation ++;
#line 209
  deviceExtension = DeviceObject__DeviceExtension;
#line 210
  tmp = IofCallDriver(deviceExtension__TargetDeviceObject, Irp);
  }
#line 212
  return (tmp);
}
}
#line 215 "diskperf_simpl1.cil.c"
int DiskPerfDispatchPower(int DeviceObject , int Irp ) 
{ int Irp__CurrentLocation;
  int Irp__Tail__Overlay__CurrentStackLocation;
  int DeviceObject__DeviceExtension;
  int deviceExtension__TargetDeviceObject;
  int deviceExtension ;
  int tmp ;

#ifdef KLEE
  klee_make_symbolic(&Irp__CurrentLocation,sizeof(Irp__CurrentLocation),"Irp__CurrentLocation");
  klee_make_symbolic(&Irp__Tail__Overlay__CurrentStackLocation,sizeof(Irp__Tail__Overlay__CurrentStackLocation),"Irp__Tail__Overlay__CurrentStackLocation");
  klee_make_symbolic(&DeviceObject__DeviceExtension,sizeof(DeviceObject__DeviceExtension),"DeviceObject__DeviceExtension");
  klee_make_symbolic(&deviceExtension__TargetDeviceObject,sizeof(deviceExtension__TargetDeviceObject),"deviceExtension__TargetDeviceObject");
#endif

  {
#line 224
  if (s == NP) {
#line 225
    s = SKIP1;
  } else {
    {
#line 228
    errorFn();
    }
  }
  {
#line 232
  Irp__CurrentLocation ++;
#line 233
  Irp__Tail__Overlay__CurrentStackLocation ++;
#line 234
  deviceExtension = DeviceObject__DeviceExtension;
#line 235
  tmp = PoCallDriver(deviceExtension__TargetDeviceObject, Irp);
  }
#line 237
  return (tmp);
}
}
#line 240 "diskperf_simpl1.cil.c"
int DiskPerfForwardIrpSynchronous(int DeviceObject , int Irp ) 
{ int Irp__Tail__Overlay__CurrentStackLocation;
  int DeviceObject__DeviceExtension;
  int deviceExtension__TargetDeviceObject;
  int deviceExtension ;
  int event;
  int status ;
  int nextIrpSp__Control ;
  int irpSp ;
  int nextIrpSp ;
  int irpSp__Context ;
  int irpSp__Control ;
  int irpSp___0 ;
  long __cil_tmp15 ;

#ifdef KLEE
  klee_make_symbolic(&Irp__Tail__Overlay__CurrentStackLocation,sizeof(Irp__Tail__Overlay__CurrentStackLocation),"Irp__Tail__Overlay__CurrentStackLocation");
  klee_make_symbolic(&DeviceObject__DeviceExtension,sizeof(DeviceObject__DeviceExtension),"DeviceObject__DeviceExtension");
  klee_make_symbolic(&deviceExtension__TargetDeviceObject,sizeof(deviceExtension__TargetDeviceObject),"deviceExtension__TargetDeviceObject");
  klee_make_symbolic(&event,sizeof(event),"event");
#endif

  {
#line 255
  deviceExtension = DeviceObject__DeviceExtension;
#line 256
  irpSp = Irp__Tail__Overlay__CurrentStackLocation;
#line 257
  nextIrpSp = Irp__Tail__Overlay__CurrentStackLocation - 1;
#line 258
  nextIrpSp__Control = 0;
#line 259
  if (s != NP) {
    {
#line 261
    errorFn();
    }
  } else {
#line 264
    if (compRegistered != 0) {
      {
#line 266
      errorFn();
      }
    } else {
#line 269
      compRegistered = 1;
#line 270
      routine = 0;
    }
  }
  {
#line 274
  irpSp___0 = Irp__Tail__Overlay__CurrentStackLocation - 1;
#line 275
  irpSp__Context = event;
#line 276
  irpSp__Control = 224;
#line 280
  status = IofCallDriver(deviceExtension__TargetDeviceObject, Irp);
  }
  {
#line 282
  __cil_tmp15 = (long )status;
#line 282
  if (__cil_tmp15 == 259L) {
    {
#line 284
    KeWaitForSingleObject(event, Executive, KernelMode, 0, 0);
#line 285
    status = myStatus;
    }
  }
  }
#line 290
  return (status);
}
}
#line 293 "diskperf_simpl1.cil.c"
int DiskPerfCreate(int DeviceObject , int Irp ) 
{ 

  {
  {
#line 298
  myStatus = 0;
#line 299
  IofCompleteRequest(Irp, 0);
  }
#line 301
  return (0);
}
}
#line 304 "diskperf_simpl1.cil.c"
int DiskPerfIoCompletion(int DeviceObject , int Irp , int Context ) 
{ int irpStack__MajorFunction;
  int partitionCounters__BytesRead__QuadPart;
  int Irp__IoStatus__Information;
  int partitionCounters__ReadCount;
  int partitionCounters__ReadTime__QuadPart;
  int difference__QuadPart;
  int partitionCounters__BytesWritten__QuadPart;
  int partitionCounters__WriteCount;
  int partitionCounters__WriteTime__QuadPart;
  int Irp__Flags;
  int partitionCounters__SplitCount;
  int Irp__PendingReturned;
  int Irp__Tail__Overlay__CurrentStackLocation__Control ;
  int partitionCounters;
  int queueLen;

#ifdef KLEE
  klee_make_symbolic(&irpStack__MajorFunction,sizeof(irpStack__MajorFunction),"irpStack__MajorFunction");
  klee_make_symbolic(&partitionCounters__BytesRead__QuadPart,sizeof(partitionCounters__BytesRead__QuadPart),"partitionCounters__BytesRead__QuadPart");
  klee_make_symbolic(&Irp__IoStatus__Information,sizeof(Irp__IoStatus__Information),"Irp__IoStatus__Information");
  klee_make_symbolic(&partitionCounters__ReadCount,sizeof(partitionCounters__ReadCount),"partitionCounters__ReadCount");
  klee_make_symbolic(&partitionCounters__ReadTime__QuadPart,sizeof(partitionCounters__ReadTime__QuadPart),"partitionCounters__ReadTime__QuadPart");
  klee_make_symbolic(&difference__QuadPart,sizeof(difference__QuadPart),"difference__QuadPart");
  klee_make_symbolic(&partitionCounters__BytesWritten__QuadPart,sizeof(partitionCounters__BytesWritten__QuadPart),"partitionCounters__BytesWritten__QuadPart");
  klee_make_symbolic(&partitionCounters__WriteCount,sizeof(partitionCounters__WriteCount),"partitionCounters__WriteCount");
  klee_make_symbolic(&partitionCounters__WriteTime__QuadPart,sizeof(partitionCounters__WriteTime__QuadPart),"partitionCounters__WriteTime__QuadPart");
  klee_make_symbolic(&Irp__Flags,sizeof(Irp__Flags),"Irp__Flags");
  klee_make_symbolic(&partitionCounters__SplitCount,sizeof(partitionCounters__SplitCount),"partitionCounters__SplitCount");
  klee_make_symbolic(&Irp__PendingReturned,sizeof(Irp__PendingReturned),"Irp__PendingReturned");
  klee_make_symbolic(&partitionCounters,sizeof(partitionCounters),"partitionCounters");
  klee_make_symbolic(&queueLen,sizeof(queueLen),"queueLen");
#endif

  {
#line 322
  if (partitionCounters == 0) {
#line 323
    return (0);
  }
#line 327
  if (queueLen < 0) {

  }
#line 332
  if (queueLen == 0) {

  }
#line 337
  if (irpStack__MajorFunction == 3) {
#line 338
    partitionCounters__BytesRead__QuadPart += Irp__IoStatus__Information;
#line 339
    partitionCounters__ReadCount ++;
#line 340
    partitionCounters__ReadTime__QuadPart += difference__QuadPart;
  } else {
#line 342
    partitionCounters__BytesWritten__QuadPart += Irp__IoStatus__Information;
#line 343
    partitionCounters__WriteCount ++;
#line 344
    partitionCounters__WriteTime__QuadPart += difference__QuadPart;
  }
#line 346
  if (Irp__Flags != 8) {
#line 347
    partitionCounters__SplitCount ++;
  }
  else {
  }
#line 351
  if (Irp__PendingReturned) {
#line 352
    if (pended == 0) {
#line 353
      pended = 1;
    } else {
      {
#line 356
      errorFn();
      }
    }
#line 359
    //Irp__Tail__Overlay__CurrentStackLocation__Control |= 1;
  }
#line 363
  return (0);
}
}
#line 366 "diskperf_simpl1.cil.c"
int DiskPerfDeviceControl(int DeviceObject , int Irp ) 
{ int Irp__CurrentLocation;
  int Irp__Tail__Overlay__CurrentStackLocation;
  int DeviceObject__DeviceExtension;
  int deviceExtension__TargetDeviceObject;
  int currentIrpStack__Parameters__DeviceIoControl__IoControlCode;
  int currentIrpStack__Parameters__DeviceIoControl__OutputBufferLength;
  int sizeof__DISK_PERFORMANCE;
  int Irp__IoStatus__Information ;
  int deviceExtension__DiskCounters;
  int Irp__AssociatedIrp__SystemBuffer;
  int deviceExtension__Processors;
  int totalCounters__QueueDepth ;
  int deviceExtension__QueueDepth;
  int Irp__IoStatus__Status ;
  int deviceExtension ;
  int currentIrpStack ;
  int status ;
  int i ;
  int totalCounters ;
  int diskCounters ;
  int tmp ;
  int __cil_tmp24 ;
  int __cil_tmp25 ;
  int __cil_tmp26 ;

#ifdef KLEE
  klee_make_symbolic(&Irp__CurrentLocation,sizeof(Irp__CurrentLocation),"Irp__CurrentLocation");
  klee_make_symbolic(&Irp__Tail__Overlay__CurrentStackLocation,sizeof(Irp__Tail__Overlay__CurrentStackLocation),"Irp__Tail__Overlay__CurrentStackLocation");
  klee_make_symbolic(&DeviceObject__DeviceExtension,sizeof(DeviceObject__DeviceExtension),"DeviceObject__DeviceExtension");
  klee_make_symbolic(&deviceExtension__TargetDeviceObject,sizeof(deviceExtension__TargetDeviceObject),"deviceExtension__TargetDeviceObject");
  klee_make_symbolic(&currentIrpStack__Parameters__DeviceIoControl__IoControlCode,sizeof(currentIrpStack__Parameters__DeviceIoControl__IoControlCode),"currentIrpStack__Parameters__DeviceIoControl__IoControlCode");
  klee_make_symbolic(&currentIrpStack__Parameters__DeviceIoControl__OutputBufferLength,sizeof(currentIrpStack__Parameters__DeviceIoControl__OutputBufferLength),"currentIrpStack__Parameters__DeviceIoControl__OutputBufferLength");
  klee_make_symbolic(&sizeof__DISK_PERFORMANCE,sizeof(sizeof__DISK_PERFORMANCE),"sizeof__DISK_PERFORMANCE");
  klee_make_symbolic(&deviceExtension__DiskCounters,sizeof(deviceExtension__DiskCounters),"deviceExtension__DiskCounters");
  klee_make_symbolic(&Irp__AssociatedIrp__SystemBuffer,sizeof(Irp__AssociatedIrp__SystemBuffer),"Irp__AssociatedIrp__SystemBuffer");
  klee_make_symbolic(&deviceExtension__Processors,sizeof(deviceExtension__Processors),"deviceExtension__Processors");
  klee_make_symbolic(&deviceExtension__QueueDepth,sizeof(deviceExtension__QueueDepth),"deviceExtension__QueueDepth");
#endif

  {
#line 390
  deviceExtension = DeviceObject__DeviceExtension;
#line 391
  currentIrpStack = Irp__Tail__Overlay__CurrentStackLocation;
  {
#line 392
  __cil_tmp24 = 32;
#line 392
  __cil_tmp25 = 458752;
#line 392
  __cil_tmp26 = 458784;
#line 392
  if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp26) {
#line 393
    if (currentIrpStack__Parameters__DeviceIoControl__OutputBufferLength < sizeof__DISK_PERFORMANCE) {
#line 394
      status = -1073741789;
#line 395
      Irp__IoStatus__Information = 0;
    } else {
#line 397
      diskCounters = deviceExtension__DiskCounters;
#line 398
      if (diskCounters == 0) {
        {
#line 400
        Irp__IoStatus__Status = -1073741823;
#line 401
        myStatus = -1073741823;
#line 402
        IofCompleteRequest(Irp, 0);
        }
#line 404
        return (-1073741823);
      }
#line 408
      totalCounters = Irp__AssociatedIrp__SystemBuffer;
#line 409
      i = 0;
      {
#line 411
      while (1) {
        while_0_continue: /* CIL Label */ ;

#line 413
        if (i >= deviceExtension__Processors) {
          goto while_1_break;
        }
#line 418
        i ++;
      }
      while_0_break: /* CIL Label */ ;
      }
      while_1_break: 
#line 422
      totalCounters__QueueDepth = deviceExtension__QueueDepth;
#line 423
      status = 0;
#line 424
      Irp__IoStatus__Information = sizeof__DISK_PERFORMANCE;
    }
    {
#line 427
    Irp__IoStatus__Status = status;
#line 428
    myStatus = status;
#line 429
    IofCompleteRequest(Irp, 0);
    }
#line 431
    return (status);
  } else {
    {
#line 434
    Irp__CurrentLocation ++;
#line 435
    Irp__Tail__Overlay__CurrentStackLocation ++;
#line 436
    tmp = IofCallDriver(deviceExtension__TargetDeviceObject, Irp);
    }
#line 438
    return (tmp);
  }
  }
}
}
#line 442 "diskperf_simpl1.cil.c"
int DiskPerfShutdownFlush(int DeviceObject , int Irp ) 
{ int DeviceObject__DeviceExtension;
  int Irp__CurrentLocation;
  int Irp__Tail__Overlay__CurrentStackLocation;
  int deviceExtension__TargetDeviceObject;
  int deviceExtension ;
  int tmp ;

#ifdef KLEE
  klee_make_symbolic(&DeviceObject__DeviceExtension,sizeof(DeviceObject__DeviceExtension),"DeviceObject__DeviceExtension");
  klee_make_symbolic(&Irp__CurrentLocation,sizeof(Irp__CurrentLocation),"Irp__CurrentLocation");
  klee_make_symbolic(&Irp__Tail__Overlay__CurrentStackLocation,sizeof(Irp__Tail__Overlay__CurrentStackLocation),"Irp__Tail__Overlay__CurrentStackLocation");
  klee_make_symbolic(&deviceExtension__TargetDeviceObject,sizeof(deviceExtension__TargetDeviceObject),"deviceExtension__TargetDeviceObject");
#endif

  {
  {
#line 452
  deviceExtension = DeviceObject__DeviceExtension;
#line 453
  Irp__CurrentLocation ++;
#line 454
  Irp__Tail__Overlay__CurrentStackLocation ++;
#line 455
  tmp = IofCallDriver(deviceExtension__TargetDeviceObject, Irp);
  }
#line 457
  return (tmp);
}
}
#line 460 "diskperf_simpl1.cil.c"
void DiskPerfUnload(int DriverObject ) 
{ 

  {
#line 464
  return;
}
}
#line 467 "diskperf_simpl1.cil.c"
int DiskPerfRegisterDevice(int DeviceObject ) 
{ int DeviceObject__DeviceExtension;
  int deviceExtension__TargetDeviceObject;
  int sizeof__number;
  int ioStatus__Status;
  int sizeof__VOLUME_NUMBER;
  int volumeNumber__VolumeManagerName__0;
  int status ;
  int ioStatus;
  int event;
  int deviceExtension ;
  int irp ;
  int number;
  int registrationFlag ;
  int sizeof__MOUNTDEV_NAME;
  int output__NameLength;
  int outputSize ;
  int output;
  int volumeNumber;
  int __cil_tmp20 ;
  int __cil_tmp21 ;
  int __cil_tmp22 ;
  long __cil_tmp23 ;
  int __cil_tmp24 ;
  int __cil_tmp25 ;
  int __cil_tmp26 ;
  long __cil_tmp27 ;
  unsigned long __cil_tmp28 ;
  int __cil_tmp29 ;
  int __cil_tmp30 ;
  int __cil_tmp31 ;
  long __cil_tmp32 ;
  int __cil_tmp33 ;
  int __cil_tmp34 ;
  int __cil_tmp35 ;
  int __cil_tmp36 ;
  long __cil_tmp37 ;
  int __cil_tmp38 ;
  int __cil_tmp39 ;

#ifdef KLEE
  klee_make_symbolic(&DeviceObject__DeviceExtension,sizeof(DeviceObject__DeviceExtension),"DeviceObject__DeviceExtension");
  klee_make_symbolic(&deviceExtension__TargetDeviceObject,sizeof(deviceExtension__TargetDeviceObject),"deviceExtension__TargetDeviceObject");
  klee_make_symbolic(&sizeof__number,sizeof(sizeof__number),"sizeof__number");
  klee_make_symbolic(&ioStatus__Status,sizeof(ioStatus__Status),"ioStatus__Status");
  klee_make_symbolic(&sizeof__VOLUME_NUMBER,sizeof(sizeof__VOLUME_NUMBER),"sizeof__VOLUME_NUMBER");
  klee_make_symbolic(&volumeNumber__VolumeManagerName__0,sizeof(volumeNumber__VolumeManagerName__0),"volumeNumber__VolumeManagerName__0");
  klee_make_symbolic(&ioStatus,sizeof(ioStatus),"ioStatus");
  klee_make_symbolic(&event,sizeof(event),"event");
  klee_make_symbolic(&number,sizeof(number),"number");
  klee_make_symbolic(&sizeof__MOUNTDEV_NAME,sizeof(sizeof__MOUNTDEV_NAME),"sizeof__MOUNTDEV_NAME");
  klee_make_symbolic(&output__NameLength,sizeof(output__NameLength),"output__NameLength");
  klee_make_symbolic(&output,sizeof(output),"output");
  klee_make_symbolic(&volumeNumber,sizeof(volumeNumber),"volumeNumber");
#endif

  {
  {
#line 489
  registrationFlag = 0;
#line 490
  deviceExtension = DeviceObject__DeviceExtension;
#line 491
  __cil_tmp20 = 4224;
#line 491
  __cil_tmp21 = 2949120;
#line 491
  __cil_tmp22 = 2953344;
#line 491
  irp = IoBuildDeviceIoControlRequest(__cil_tmp22, deviceExtension__TargetDeviceObject,
                                      0, 0, number, sizeof__number, 0, event, ioStatus);
  }
#line 494
  if (! irp) {
#line 495
    return (-1073741670);
  }
  {
#line 500
  status = IofCallDriver(deviceExtension__TargetDeviceObject, irp);
  }
  {
#line 502
  __cil_tmp23 = (long )status;
#line 502
  if (__cil_tmp23 == 259L) {
    {
#line 504
    KeWaitForSingleObject(event, Executive, KernelMode, 0, 0);
#line 505
    status = ioStatus__Status;
    }
  }
  }
#line 510
  if (status < 0) {
#line 513
    outputSize = sizeof__MOUNTDEV_NAME;
#line 514
    if (! output) {
#line 515
      return (-1073741670);
    }
    {
#line 520
    __cil_tmp24 = 8;
#line 520
    __cil_tmp25 = 5046272;
#line 520
    __cil_tmp26 = 5046280;
#line 520
    irp = IoBuildDeviceIoControlRequest(__cil_tmp26, deviceExtension__TargetDeviceObject,
                                        0, 0, output, outputSize, 0, event, ioStatus);
    }
#line 523
    if (! irp) {
#line 524
      return (-1073741670);
    }
    {
#line 529
    status = IofCallDriver(deviceExtension__TargetDeviceObject, irp);
    }
    {
#line 531
    __cil_tmp27 = (long )status;
#line 531
    if (__cil_tmp27 == 259L) {
      {
#line 533
      KeWaitForSingleObject(event, Executive, KernelMode, 0, 0);
#line 534
      status = ioStatus__Status;
      }
    }
    }
    {
#line 539
    __cil_tmp28 = (unsigned long )status;
#line 539
    if (__cil_tmp28 == -2147483643) {
#line 540
      outputSize = sizeof__MOUNTDEV_NAME + output__NameLength;
#line 541
      if (! output) {
#line 542
        return (-1073741670);
      }
      {
#line 547
      __cil_tmp29 = 8;
#line 547
      __cil_tmp30 = 5046272;
#line 547
      __cil_tmp31 = 5046280;
#line 547
      irp = IoBuildDeviceIoControlRequest(__cil_tmp31, deviceExtension__TargetDeviceObject,
                                          0, 0, output, outputSize, 0, event, ioStatus);
      }
#line 550
      if (! irp) {
#line 551
        return (-1073741670);
      }
      {
#line 556
      status = IofCallDriver(deviceExtension__TargetDeviceObject, irp);
      }
      {
#line 558
      __cil_tmp32 = (long )status;
#line 558
      if (__cil_tmp32 == 259L) {
        {
#line 560
        KeWaitForSingleObject(event, Executive, KernelMode, 0, 0);
#line 561
        status = ioStatus__Status;
        }
      }
      }
    }
    }
    {
#line 569
    if (status < 0) {
#line 570
      return (status);
    }
    }
    {
#line 575
    __cil_tmp34 = 28;
#line 575
    __cil_tmp35 = 5636096;
#line 575
    __cil_tmp36 = 5636124;
#line 575
    irp = IoBuildDeviceIoControlRequest(__cil_tmp36, deviceExtension__TargetDeviceObject,
                                        0, 0, volumeNumber, sizeof__VOLUME_NUMBER,
                                        0, event, ioStatus);
    }
#line 579
    if (! irp) {
#line 580
      return (-1073741670);
    }
    {
#line 585
    status = IofCallDriver(deviceExtension__TargetDeviceObject, irp);
    }
    {
#line 587
    __cil_tmp37 = (long )status;
#line 587
    if (__cil_tmp37 == 259L) {
      {
#line 589
      KeWaitForSingleObject(event, Executive, KernelMode, 0, 0);
#line 590
      status = ioStatus__Status;
      }
    }
    }
    {
#line 595
    if (status < 0) {
      goto _L;
    } else {
#line 598
      if (volumeNumber__VolumeManagerName__0 == 0) {
        _L: 
#line 600
        if (status >= 0) {

        }
      }
    }
    }
  }
  {
#line 610
#line 610
  if (status < 0) {

  }
  }
#line 615
  return (status);
}
}
#line 618 "diskperf_simpl1.cil.c"
void stub_driver_init(void) 
{ 

  {
#line 622
  s = NP;
#line 623
  customIrp = 0;
#line 624
  setEventCalled = customIrp;
#line 625
  lowerDriverReturn = setEventCalled;
#line 626
  compRegistered = lowerDriverReturn;
#line 627
  compFptr = compRegistered;
#line 628
  pended = compFptr;
#line 629
  return;
}
}
#line 632 "diskperf_simpl1.cil.c"
int main() 
{ int d;
  int status;
  int we_should_unload;
  int irp;
  int pirp__IoStatus__Status ;
  int irp_choice;
  int devobj;
  int __cil_tmp9 ;

#ifdef KLEE
  klee_make_symbolic(&d,sizeof(d),"d");
  klee_make_symbolic(&status,sizeof(status),"status");
  klee_make_symbolic(&we_should_unload,sizeof(we_should_unload),"we_should_unload");
  klee_make_symbolic(&irp,sizeof(irp),"irp");
  klee_make_symbolic(&irp_choice,sizeof(irp_choice),"irp_choice");
  klee_make_symbolic(&devobj,sizeof(devobj),"devobj");
#endif

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
 routine  = 0;
 pirp  = 0;
 Executive  = 0;
 KernelMode  = 0;

  {
  {
#line 644
  pirp = irp;
#line 645
  _BLAST_init();
  }
#line 647
  if (status >= 0) {
#line 648
    s = NP;
#line 649
    customIrp = 0;
#line 650
    setEventCalled = customIrp;
#line 651
    lowerDriverReturn = setEventCalled;
#line 652
    compRegistered = lowerDriverReturn;
#line 653
    compFptr = compRegistered;
#line 654
    pended = compFptr;
#line 655
    pirp__IoStatus__Status = 0;
#line 656
    myStatus = 0;
#line 657
    if (irp_choice == 0) {
#line 658
      pirp__IoStatus__Status = -1073741637;
#line 659
      myStatus = -1073741637;
    }
    {
#line 664
    stub_driver_init();
    }
    {
#line 666
    if (status < 0) {
#line 667
      return (-1);
    }
    }
#line 671
    int tmp_ndt_1;
    tmp_ndt_1;

#ifdef KLEE
    klee_make_symbolic(&tmp_ndt_1,sizeof(tmp_ndt_1),"tmp_ndt_1");
#endif
    if (tmp_ndt_1 == 0) {
      goto switch_2_0;
    } else {
#line 674
      int tmp_ndt_2;
      tmp_ndt_2;

#ifdef KLEE
      klee_make_symbolic(&tmp_ndt_2,sizeof(tmp_ndt_2),"tmp_ndt_2");
#endif
      if (tmp_ndt_2 == 2) {
        goto switch_2_2;
      } else {
#line 677
        int tmp_ndt_3;
        tmp_ndt_3;

#ifdef KLEE
	klee_make_symbolic(&tmp_ndt_3,sizeof(tmp_ndt_3),"tmp_ndt_3");
#endif
        if (tmp_ndt_3 == 3) {
          goto switch_2_3;
        } else {
#line 680
	  int tmp_ndt_4;
	  tmp_ndt_4;

#ifdef KLEE
	  klee_make_symbolic(&tmp_ndt_4,sizeof(tmp_ndt_4),"tmp_ndt_4");
#endif
          if (tmp_ndt_4 == 4) {
            goto switch_2_4;
          } else {
#line 683
	    int tmp_ndt_5;
	    tmp_ndt_5;

#ifdef KLEE
	    klee_make_symbolic(&tmp_ndt_5,sizeof(tmp_ndt_5),"tmp_ndt_5");
#endif
            if (tmp_ndt_5 == 12) {
              goto switch_2_12;
            } else {
              goto switch_2_default;
#line 688
              if (0) {
                switch_2_0: 
                {
#line 691
                status = DiskPerfCreate(devobj, pirp);
                }
                goto switch_2_break;
                switch_2_2: 
                {
#line 696
                status = DiskPerfDeviceControl(devobj, pirp);
                }
                goto switch_2_break;
                switch_2_3: 
                {
#line 701
                status = DiskPerfDispatchPnp(devobj, pirp);
                }
                goto switch_2_break;
                switch_2_4: 
                {
#line 706
                status = DiskPerfDispatchPower(devobj, pirp);
                }
                goto switch_2_break;
                switch_2_12: 
                {
#line 711
                status = DiskPerfShutdownFlush(devobj, pirp);
                }
                goto switch_2_break;
                switch_2_default: ;
#line 715
                return (-1);
              } else {
                switch_2_break: ;
              }
            }
          }
        }
      }
    }
#line 725
    if (we_should_unload) {
      {
#line 727
      DiskPerfUnload(d);
      }
    }
  }
#line 735
  if (pended == 1) {
#line 736
    if (s == NP) {
#line 737
      s = NP;
    } else {
      goto _L___2;
    }
  } else {
    _L___2: 
#line 743
    if (pended == 1) {
#line 744
      if (s == MPR3) {
#line 745
        s = MPR3;
      } else {
        goto _L___1;
      }
    } else {
      _L___1: 
#line 751
      if (s != UNLOADED) {
#line 754
        if (status != -1) {
#line 757
          if (s != SKIP2) {
#line 758
            if (s != IPC) {
#line 759
              if (s != DC) {
                {
#line 761
                errorFn();
                }
              } else {
                goto _L___0;
              }
            } else {
              goto _L___0;
            }
          } else {
            _L___0: 
#line 771
            if (pended == 1) {
#line 772
              if (status != 259) {
                {
#line 774
                errorFn();
                }
              }
            } else {
#line 780
              if (s == DC) {
#line 781
                if (status == 259) {
                  {
#line 783
                  errorFn();
                  }
                }
              } else {
#line 789
                if (status != lowerDriverReturn) {
                  {
#line 791
                  errorFn();
                  }
                }
              }
            }
          }
        }
      }
    }
  }
#line 803
  return (status);
}
}
#line 806 "diskperf_simpl1.cil.c"
int IoBuildDeviceIoControlRequest(int IoControlCode , int DeviceObject , int InputBuffer ,
                                  int InputBufferLength , int OutputBuffer , int OutputBufferLength ,
                                  int InternalDeviceIoControl , int Event , int IoStatusBlock ) 
{
  int malloc_ret;

#ifdef KLEE
  klee_make_symbolic(&malloc_ret,sizeof(malloc_ret),"malloc_ret");
#endif

  {
#line 813
  customIrp = 1;
#line 814
  int tmp_ndt_7;
  tmp_ndt_7;

#ifdef KLEE
  klee_make_symbolic(&tmp_ndt_7,sizeof(tmp_ndt_7),"tmp_ndt_7");
#endif
  if (tmp_ndt_7 == 0) {
    goto switch_3_0;
  } else {
    goto switch_3_default;
#line 819
    if (0) {
      switch_3_0: ;
#line 821
      return (malloc_ret);
      switch_3_default: ;
#line 823
      return (0);
    } else {

    }
  }
}
}
#line 831 "diskperf_simpl1.cil.c"
void stubMoreProcessingRequired(void) 
{ 

  {
#line 835
  if (s == NP) {
#line 836
    s = MPR1;
  } else {
    {
#line 839
    errorFn();
    }
  }
#line 842
  return;
}
}
#line 845 "diskperf_simpl1.cil.c"
int IofCallDriver(int DeviceObject , int Irp ) 
{
  int returnVal2 ;
  int compRetStatus ;
  int lcontext;

#ifdef KLEE
  klee_make_symbolic(&lcontext,sizeof(lcontext),"lcontext");
#endif
  unsigned long __cil_tmp7 ;

  {
#line 852
  if (compRegistered) {
#line 853
    if (routine == 0) {
      {
#line 855
      compRetStatus = DiskPerfIrpCompletion(DeviceObject, Irp, lcontext);
      }
    } else {
      {
#line 859
      compRetStatus = DiskPerfIoCompletion(DeviceObject, Irp, lcontext);
      }
    }
    {
#line 862
    __cil_tmp7 = (unsigned long )compRetStatus;
#line 862
    if (__cil_tmp7 == -1073741802) {
      {
#line 864
      stubMoreProcessingRequired();
      }
    }
    }
  }
#line 872
  int tmp_ndt_8;
  tmp_ndt_8;

#ifdef KLEE
  klee_make_symbolic(&tmp_ndt_8,sizeof(tmp_ndt_8),"tmp_ndt_8");
#endif
  if (tmp_ndt_8 == 0) {
    goto switch_4_0;
  } else {
#line 875
  int tmp_ndt_9;
  tmp_ndt_9;

#ifdef KLEE
  klee_make_symbolic(&tmp_ndt_9,sizeof(tmp_ndt_9),"tmp_ndt_9");
#endif
    if (tmp_ndt_9 == 1) {
      goto switch_4_1;
    } else {
      goto switch_4_default;
#line 880
      if (0) {
        switch_4_0: 
#line 882
        returnVal2 = 0;
        goto switch_4_break;
        switch_4_1: 
#line 885
        returnVal2 = -1073741823;
        goto switch_4_break;
        switch_4_default: 
#line 888
        returnVal2 = 259;
        goto switch_4_break;
      } else {
        switch_4_break: ;
      }
    }
  }
#line 896
  if (s == NP) {
#line 897
    s = IPC;
#line 898
    lowerDriverReturn = returnVal2;
  } else {
#line 900
    if (s == MPR1) {
#line 901
      if (returnVal2 == 259) {
#line 902
        s = MPR3;
#line 903
        lowerDriverReturn = returnVal2;
      } else {
#line 905
        s = NP;
#line 906
        lowerDriverReturn = returnVal2;
      }
    } else {
#line 909
      if (s == SKIP1) {
#line 910
        s = SKIP2;
#line 911
        lowerDriverReturn = returnVal2;
      } else {
        {
#line 914
        errorFn();
        }
      }
    }
  }
#line 919
  return (returnVal2);
}
}
#line 922 "diskperf_simpl1.cil.c"
void IofCompleteRequest(int Irp , int PriorityBoost ) 
{ 

  {
#line 926
  if (s == NP) {
#line 927
    s = DC;
  } else {
    {
#line 930
    errorFn();
    }
  }
#line 933
  return;
}
}
#line 936 "diskperf_simpl1.cil.c"
int KeSetEvent(int Event , int Increment , int Wait ) 
{ int l;

#ifdef KLEE
	klee_make_symbolic(&l,sizeof(l),"l");
#endif

  {
#line 940
  setEventCalled = 1;
#line 941
  return (l);
}
}
#line 944 "diskperf_simpl1.cil.c"
int KeWaitForSingleObject(int Object , int WaitReason , int WaitMode , int Alertable ,
                          int Timeout ) 
{

  {
#line 949
  if (s == MPR3) {
#line 950
    if (setEventCalled == 1) {
#line 951
      s = NP;
#line 952
      setEventCalled = 0;
    } else {
      goto _L;
    }
  } else {
    _L: 
#line 958
    if (customIrp == 1) {
#line 959
      s = NP;
#line 960
      customIrp = 0;
    } else {
#line 962
      if (s == MPR3) {
        {
#line 964
        errorFn();
        }
      }
    }
  }
#line 971
  int tmp_ndt_10;
  tmp_ndt_10;

#ifdef KLEE
  klee_make_symbolic(&tmp_ndt_10,sizeof(tmp_ndt_10),"tmp_ndt_10");
#endif
  if (tmp_ndt_10 == 0) {
    goto switch_5_0;
  } else {
    goto switch_5_default;
#line 976
    if (0) {
      switch_5_0: ;
#line 978
      return (0);
      switch_5_default: ;
#line 980
      return (-1073741823);
    } else {

    }
  }
}
}
#line 988 "diskperf_simpl1.cil.c"
int PoCallDriver(int DeviceObject , int Irp ) 
{
  int compRetStatus ;
  int returnVal ;
  int lcontext;

#ifdef KLEE
  klee_make_symbolic(&lcontext,sizeof(lcontext),"lcontext");
#endif
  unsigned long __cil_tmp7 ;
  long __cil_tmp8 ;

  {
#line 995
  if (compRegistered) {
#line 996
    if (routine == 0) {
      {
#line 998
      compRetStatus = DiskPerfIrpCompletion(DeviceObject, Irp, lcontext);
      }
    } else {
#line 1001
      if (routine == 1) {
        {
#line 1003
        compRetStatus = DiskPerfIoCompletion(DeviceObject, Irp, lcontext);
        }
      }
    }
    {
#line 1009
    __cil_tmp7 = (unsigned long )compRetStatus;
#line 1009
    if (__cil_tmp7 == -1073741802) {
      {
#line 1011
      stubMoreProcessingRequired();
      }
    }
    }
  }
#line 1019
  int tmp_ndt_11;
  tmp_ndt_11;

#ifdef KLEE
  klee_make_symbolic(&tmp_ndt_11,sizeof(tmp_ndt_11),"tmp_ndt_11");
#endif
  if (tmp_ndt_11 == 0) {
    goto switch_6_0;
  } else {
#line 1022
  int tmp_ndt_12;
  tmp_ndt_12;

#ifdef KLEE
  klee_make_symbolic(&tmp_ndt_12,sizeof(tmp_ndt_12),"tmp_ndt_12");
#endif
    if (tmp_ndt_12 == 1) {
      goto switch_6_1;
    } else {
      goto switch_6_default;
#line 1027
      if (0) {
        switch_6_0: 
#line 1029
        returnVal = 0;
        goto switch_6_break;
        switch_6_1: 
#line 1032
        returnVal = -1073741823;
        goto switch_6_break;
        switch_6_default: 
#line 1035
        returnVal = 259;
        goto switch_6_break;
      } else {
        switch_6_break: ;
      }
    }
  }
#line 1043
  if (s == NP) {
#line 1044
    s = IPC;
#line 1045
    lowerDriverReturn = returnVal;
  } else {
#line 1047
    if (s == MPR1) {
      {
#line 1048
      __cil_tmp8 = (long )returnVal;
#line 1048
      if (__cil_tmp8 == 259L) {
#line 1049
        s = MPR3;
#line 1050
        lowerDriverReturn = returnVal;
      } else {
#line 1052
        s = NP;
#line 1053
        lowerDriverReturn = returnVal;
      }
      }
    } else {
#line 1056
      if (s == SKIP1) {
#line 1057
        s = SKIP2;
#line 1058
        lowerDriverReturn = returnVal;
      } else {
        {
#line 1061
        errorFn();
        }
      }
    }
  }
#line 1066
  return (returnVal);
}
}
