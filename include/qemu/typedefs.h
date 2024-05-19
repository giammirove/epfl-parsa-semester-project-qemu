#ifndef QEMU_TYPEDEFS_H
#define QEMU_TYPEDEFS_H
#include <bits/pthreadtypes.h>
#include <bits/stdint-uintn.h>

/*
 * This header is for selectively avoiding #include just to get a
 * typedef name.
 *
 * Declaring a typedef name in its "obvious" place can result in
 * inclusion cycles, in particular for complete struct and union
 * types that need more types for their members.  It can also result
 * in headers pulling in many more headers, slowing down builds.
 *
 * You can break such cycles and unwanted dependencies by declaring
 * the typedef name here.
 *
 * For struct types used in only a few headers, judicious use of the
 * struct tag instead of the typedef name is commonly preferable.
 */

/*
 * Incomplete struct types
 * Please keep this list in case-insensitive alphabetical order.
 */
typedef struct AccelCPUState AccelCPUState;
typedef struct AccelState AccelState;
typedef struct AdapterInfo AdapterInfo;
typedef struct AddressSpace AddressSpace;
typedef struct AioContext AioContext;
typedef struct Aml Aml;
typedef struct AnnounceTimer AnnounceTimer;
typedef struct ArchCPU ArchCPU;
typedef struct BdrvDirtyBitmap BdrvDirtyBitmap;
typedef struct BdrvDirtyBitmapIter BdrvDirtyBitmapIter;
typedef struct BlockBackend BlockBackend;
typedef struct BlockBackendRootState BlockBackendRootState;
typedef struct BlockDriverState BlockDriverState;
typedef struct BusClass BusClass;
typedef struct BusState BusState;
typedef struct Chardev Chardev;
typedef struct Clock Clock;
typedef struct CompatProperty CompatProperty;
typedef struct ConfidentialGuestSupport ConfidentialGuestSupport;
typedef struct CPUAddressSpace CPUAddressSpace;
typedef struct CPUArchState CPUArchState;
typedef struct CPUPluginState CPUPluginState;
typedef struct CpuInfoFast CpuInfoFast;
typedef struct CPUJumpCache CPUJumpCache;
typedef struct CPUState CPUState;
typedef struct CPUTLBEntryFull CPUTLBEntryFull;
typedef struct DeviceListener DeviceListener;
typedef struct DeviceState DeviceState;
typedef struct DirtyBitmapSnapshot DirtyBitmapSnapshot;
typedef struct DisplayChangeListener DisplayChangeListener;
typedef struct DriveInfo DriveInfo;
typedef struct DumpState DumpState;
typedef struct Error Error;
typedef struct EventNotifier EventNotifier;
typedef struct FlatView FlatView;
typedef struct FWCfgEntry FWCfgEntry;
typedef struct FWCfgIoState FWCfgIoState;
typedef struct FWCfgMemState FWCfgMemState;
typedef struct FWCfgState FWCfgState;
typedef struct GraphicHwOps GraphicHwOps;
typedef struct HostMemoryBackend HostMemoryBackend;
typedef struct I2CBus I2CBus;
typedef struct I2SCodec I2SCodec;
typedef struct IOMMUMemoryRegion IOMMUMemoryRegion;
typedef struct ISABus ISABus;
typedef struct ISADevice ISADevice;
typedef struct IsaDma IsaDma;
typedef struct JSONWriter JSONWriter;
typedef struct MACAddr MACAddr;
typedef struct MachineClass MachineClass;
typedef struct MachineState MachineState;
typedef struct MemoryListener MemoryListener;
typedef struct MemoryMappingList MemoryMappingList;
typedef struct MemoryRegion MemoryRegion;
typedef struct MemoryRegionCache MemoryRegionCache;
typedef struct MemoryRegionSection MemoryRegionSection;
typedef struct MigrationIncomingState MigrationIncomingState;
typedef struct MigrationState MigrationState;
typedef struct Monitor Monitor;
typedef struct MonitorDef MonitorDef;
typedef struct MSIMessage MSIMessage;
typedef struct NetClientState NetClientState;
typedef struct NetFilterState NetFilterState;
typedef struct NICInfo NICInfo;
typedef struct NodeInfo NodeInfo;
typedef struct NumaNodeMem NumaNodeMem;
typedef struct Object Object;
typedef struct ObjectClass ObjectClass;
typedef struct PCIBridge PCIBridge;
typedef struct PCIBus PCIBus;
typedef struct PCIDevice PCIDevice;
typedef struct PCIEAERErr PCIEAERErr;
typedef struct PCIEAERLog PCIEAERLog;
typedef struct PCIEAERMsg PCIEAERMsg;
typedef struct PCIEPort PCIEPort;
typedef struct PCIESlot PCIESlot;
typedef struct PCIESriovPF PCIESriovPF;
typedef struct PCIESriovVF PCIESriovVF;
typedef struct PCIExpressDevice PCIExpressDevice;
typedef struct PCIExpressHost PCIExpressHost;
typedef struct PCIHostDeviceAddress PCIHostDeviceAddress;
typedef struct PCIHostState PCIHostState;
typedef struct PICCommonState PICCommonState;
typedef struct PostcopyDiscardState PostcopyDiscardState;
typedef struct Property Property;
typedef struct PropertyInfo PropertyInfo;
typedef struct QBool QBool;
typedef struct QDict QDict;
typedef struct QEMUBH QEMUBH;
typedef struct QemuConsole QemuConsole;
typedef struct QEMUCursor QEMUCursor;
typedef struct QEMUFile QEMUFile;
typedef struct QemuLockable QemuLockable;
typedef struct QemuMutex QemuMutex;
typedef struct QemuOpt QemuOpt;
typedef struct QemuOpts QemuOpts;
typedef struct QemuOptsList QemuOptsList;
typedef struct QEMUSGList QEMUSGList;
typedef struct QemuSpin QemuSpin;
typedef struct QEMUTimer QEMUTimer;
typedef struct QEMUTimerListGroup QEMUTimerListGroup;
typedef struct QflexPluginState QflexPluginState;
typedef struct QList QList;
typedef struct QNull QNull;
typedef struct QNum QNum;
typedef struct QObject QObject;
typedef struct QString QString;
typedef struct RAMBlock RAMBlock;
typedef struct Range Range;
typedef struct ReservedRegion ReservedRegion;
typedef struct SHPCDevice SHPCDevice;
typedef struct SSIBus SSIBus;
typedef struct TCGCPUOps TCGCPUOps;
typedef struct TCGHelperInfo TCGHelperInfo;
typedef struct TranslationBlock TranslationBlock;
typedef struct VirtIODevice VirtIODevice;
typedef struct Visitor Visitor;
typedef struct VMChangeStateEntry VMChangeStateEntry;
typedef struct VMStateDescription VMStateDescription;

/*
 * Pointer types
 * Such typedefs should be limited to cases where the typedef's users
 * are oblivious of its "pointer-ness".
 * Please keep this list in case-insensitive alphabetical order.
 */
typedef struct IRQState *qemu_irq;

/*
 * Function types
 */
typedef void (*qemu_irq_handler)(void *opaque, int n, int level);

/**
 * TODO qflex:
 */
enum { ST_F = 0, ST_N = 1, ST_B = 2 };
struct QflexPluginState {
  int64_t n_nodes;         /* number of nodes in the simulation */
  int64_t can_count;       /* decide whether the synchronization can be done */
  int64_t idle_cpus;       /* number of cpus in idle */
  int64_t pkt_sent;        /* number of packet sent in the current quanta */
  int64_t pkt_received;    /* number of packet received (not delivered) in
                               the current quanta */
  void *pkt_list_received; /* GList * of QflexPacket - list of packet received
                              in the current quanta */
  void *pkt_list_send; /* GList * of QflexIOV - list of packet to send at the
                          beginning of the next quanta (NOT used at the moment,
                          but could be part of an optimization) */
  int64_t
      offset_time; /* "qemu" virtual clock before qflex simulation started */

  _Atomic int64_t stop;  /* decide whether you can send a network packet and
                            threads can run */
  _Atomic int64_t clock; /* new virtual time */

  /* locks for synchronization: pthread_mutex_t */
  pthread_mutex_t lock1;
  pthread_mutex_t lock2;
  pthread_mutex_t lock3;
  pthread_mutex_t *locks; /* in case you need an array of them */

  /* local struct (to access only from the plugin) */
  void *lstate;
  /* for debug purposes */
  void *dummy;

  int64_t (*get_clock)(
      void *); /* hook to the plugin to return the current clock */
  int64_t (*get_icount)(
      void *); /* hook to the plugin to return the current instruction count */
  int (*vm_pause)(void *);   /* pause the virtual clock */
  int (*vm_unpause)(void *); /* unpause the virtual clock */
  int (*pkt_notify)(int);  /* notify the sender that we received the packet, but
                              not yet  delivered ... waiting for quanta to end */
  int (*pkt_receive)(int); /* deliver all packets received during the quanta */
  int (*pkt_send)(
      void); /* send all packets not sent because in reduction phase */
  int (*send_boot)(void); /* signal the central server that we are to join the
                             multinode simulation */
  int64_t (*can_send)(void *); /* decide whether the we can send out packekts
                                (in reduction phase we can not) */
};

struct QflexPacket {
  void *tap_state; /* TAPState */
  uint8_t *buf;    /* body of the packet */
  int size;        /* size of the packet */
};
struct QflexIOV {
  void *tap_state; /* TAPState */
  struct iovec *iov;
  int iovcnt;
};

#endif /* QEMU_TYPEDEFS_H */
