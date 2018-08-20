/* SPDX-License-Identifier: BSD-3-Clause
 * Copyright 2017 Mellanox Technologies, Ltd
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>
#include <sys/types.h>
#include <sys/queue.h>
#include <netinet/in.h>
#include <setjmp.h>
#include <stdarg.h>
#include <ctype.h>
#include <errno.h>
#include <getopt.h>
#include <signal.h>
#include <stdbool.h>
#include <time.h>

#include <rte_eal.h>
#include <rte_common.h>
#include <rte_malloc.h>
#include <rte_ether.h>
#include <rte_ethdev.h>
#include <rte_mempool.h>
#include <rte_mbuf.h>
#include <rte_net.h>
#include <rte_flow.h>
#include <rte_cycles.h>
#include <rte_hash.h>
#include <rte_hash_crc.h>

#define CHECK_INTERVAL 1000  /* 100ms */
#define MAX_REPEAT_TIMES 90  /* 9s (90 * 100ms) in total */
#define TCP_FIN_FLAG 0x01
#define DEFAULT_HASH_FUNC       rte_hash_crc
#define CON_HASH_ENTRIES 500000
#define ISLINUX 1
#define ISWINDOWNS 2
#define UNKNOWNOS 3
#define APPNUM 2
#define ISWECHAT 0
#define IS360 1
#define UNKNOWN -1
#define NOTTCP -2
#define SCANINTERVAL 500
#define VALIDTIMEDURATION 250
#define VALIDSPEEDSFORWECHAT 10000
#define VALIDSPEEDSFOR360 10000

typedef struct rte_hash lookup_struct_t;

typedef struct ipv4_2tuple{
    uint32_t cli_ip;
    uint16_t cli_port;
}ipv4_2tuple;

typedef struct mIpv4{
    uint8_t ipByteMode[4];
}mIpv4;

typedef struct connect_statis_info{
    uint64_t firstTime;
    uint64_t lastTime;
    uint64_t totalBytes;
    uint8_t osFlag;
    uint8_t appFlag; //1 represent wechat,2 represent 360
    struct connect_statis_info *next;
}connect_statis_info,*connect_statis_info_p;

static connect_statis_info_p connStatInfoTable[CON_HASH_ENTRIES];
static connect_statis_info connStatInfoEntries[CON_HASH_ENTRIES];
static connect_statis_info_p unusedHead;
static connect_statis_info_p unusedTail;
static lookup_struct_t *connectionHashTable;

uint32_t *appsIpSegPool[APPNUM];

mIpv4 ip1={
    .ipByteMode={14,17,43,34},
};
mIpv4 ip2={
    .ipByteMode={113,96,233,139},
};
mIpv4 ip3={
    .ipByteMode={140,206,78,0},
};
mIpv4 ip4={
    .ipByteMode={140,206,78,255},
};
static volatile bool force_quit;

static uint16_t port_id;
static uint16_t nr_queues = 1;
struct rte_mempool *mbuf_pool;

static uint32_t convertIpFromByteToUint(mIpv4 ipv4Addr){
    uint32_t ipIntMode=0;
    int i;
    for(i=0;i<3;i++){
        ipIntMode|=ipv4Addr.ipByteMode[i];
        ipIntMode<<=8;
    }
    ipIntMode|=ipv4Addr.ipByteMode[i];
    return ipIntMode;
}

static void initConnStatInfoEntries(void){
    int i;
    for(i=0;i<CON_HASH_ENTRIES-1;i++){
        (*(connStatInfoEntries+i)).next=(connStatInfoEntries+i+1);
    }
    unusedHead=connStatInfoEntries;
    unusedTail=connStatInfoEntries+i;
}

static void addAppIpSegment(void){
    uint32_t *app1IpSegment=(uint32_t *)malloc(4*sizeof(uint32_t));
    uint32_t *app2IpSegment=(uint32_t *)malloc(2*sizeof(uint32_t));
    app1IpSegment[0]=convertIpFromByteToUint(ip1);
    app1IpSegment[1]=convertIpFromByteToUint(ip1);
    app1IpSegment[2]=convertIpFromByteToUint(ip2);
    app1IpSegment[3]=convertIpFromByteToUint(ip2);
    app2IpSegment[0]=convertIpFromByteToUint(ip3);
    app2IpSegment[1]=convertIpFromByteToUint(ip4);
    printf("%u %u %u %u\n",app1IpSegment[0],app1IpSegment[2],app2IpSegment[0],app2IpSegment[1]);
    appsIpSegPool[0]=app1IpSegment;
    appsIpSegPool[1]=app2IpSegment;
}

static int ipIsBelongToThisApp(uint32_t *appIpSegment,struct ipv4_hdr *ipv4Hdr,uint8_t appFlag){
    uint32_t sAddr=rte_be_to_cpu_32(ipv4Hdr->src_addr);
    uint32_t dAddr=rte_be_to_cpu_32(ipv4Hdr->dst_addr);
    if(appFlag==ISWECHAT){
	int i;
        for(i=0;i<4;i+=2){
            if((sAddr>=appIpSegment[i])&&(sAddr<=appIpSegment[i+1])) return 1;
            if((dAddr>=appIpSegment[i])&&(dAddr<=appIpSegment[i+1])) return 0;
        }
    }else if(appFlag==IS360){
	int i;
        for(i=0;i<2;i+=2){
            if((sAddr>=appIpSegment[i])&&(sAddr<=appIpSegment[i+1])) return 1;
            if((dAddr>=appIpSegment[i])&&(dAddr<=appIpSegment[i+1])) return 0;
        }
    }
    return -1;
}

static int getConnHashKey(struct ipv4_hdr *ipv4Hdr,ipv4_2tuple *key){
    struct tcp_hdr *tcpHdr;
    if(ipv4Hdr->next_proto_id==IPPROTO_TCP){
        tcpHdr=(struct tcp_hdr *)((unsigned char *)ipv4Hdr+sizeof(struct ipv4_hdr));
    }else{
        return NOTTCP;
    }
    int ret;    //ret consist of edge and packet's app type,edge declare where is packet from(client or server).
    int edge;
    edge=ipIsBelongToThisApp(appsIpSegPool[ISWECHAT],ipv4Hdr,ISWECHAT);
    if(edge==0){
        key->cli_ip=rte_be_to_cpu_32(ipv4Hdr->src_addr);
        key->cli_port=rte_be_to_cpu_16(tcpHdr->src_port);
        ret=((edge<<16)|ISWECHAT);
        return ret;
    }
    if(edge==1){
        key->cli_ip=rte_be_to_cpu_32(ipv4Hdr->dst_addr);
        key->cli_port=rte_be_to_cpu_16(tcpHdr->dst_port);
        ret=((edge<<16)|ISWECHAT);
        return ret;
    }
    edge=ipIsBelongToThisApp(appsIpSegPool[IS360],ipv4Hdr,IS360);
    if(edge==0){
        key->cli_ip=rte_be_to_cpu_32(ipv4Hdr->src_addr);
        key->cli_port=rte_be_to_cpu_16(tcpHdr->src_port);
        ret=((edge<<16)|IS360);
        return ret;
    }
    if(edge==1){
        key->cli_ip=rte_be_to_cpu_32(ipv4Hdr->dst_addr);
        key->cli_port=rte_be_to_cpu_16(tcpHdr->dst_port);
        ret=((edge<<16)|IS360);
        return ret;
    }
    return UNKNOWN;
}

//get socketid by socketid = rte_lcore_to_socket_id(lcore_id) or rte_socket_id().
static void setup_hash(int socketid)
{
	struct rte_hash_parameters con_hash_params = {
        	.name = NULL,
		.entries = CON_HASH_ENTRIES,
		.key_len = sizeof(struct ipv4_2tuple),
		.hash_func = DEFAULT_HASH_FUNC,
		.hash_func_init_val = 0,
	};
	//unsigned i;
	//int ret;
	char s[64];

	/* create ipv4 hash */
	snprintf(s, sizeof(s), "connectionHashTable%d", socketid);
	con_hash_params.name = s;
	con_hash_params.socket_id = socketid;
    	connectionHashTable=rte_hash_create(&con_hash_params);
	if (connectionHashTable == NULL)
		rte_exit(EXIT_FAILURE, "Unable to create the l3fwd hash on "
				"socket %d\n", socketid);
	printf("setup hashtable ok!\n");
}

static int updateConnStatInfo(struct ipv4_hdr *ipv4Hdr,ipv4_2tuple *key,int edge,int appFlag){
    struct tcp_hdr *tcpHdr=(struct tcp_hdr *)((unsigned char *)ipv4Hdr+sizeof(struct ipv4_hdr));
    int index=rte_hash_lookup(connectionHashTable,(const void *)key);
    if(index==-EINVAL){
        printf("invalid parameters in hash lookup!\n");
        return -1;
    }else if(index==-ENOENT){
        if((tcpHdr->tcp_flags&TCP_FIN_FLAG)==0){
            index=rte_hash_add_key(connectionHashTable,(const void *)key);
            if(index==-EINVAL){
                printf("invalid parameters in hash add!\n");
                return -1;
            }else if(index==-ENOSPC){
                printf("there is no more space in hash table!\n");
                return -2;
            }else{
                if(unusedHead==NULL){
                    printf("there is no more space to store connection statistics info!\n");
                    return -2;
                }else{
                    connStatInfoTable[index]=unusedHead;
                    unusedHead=unusedHead->next;
                    connStatInfoTable[index]->next=NULL;
                    connStatInfoTable[index]->firstTime=connStatInfoTable[index]->lastTime=rte_rdtsc();
                    connStatInfoTable[index]->totalBytes+=ipv4Hdr->total_length;
                    if(appFlag==0){
                        connStatInfoTable[index]->appFlag=1;
                    }else if(appFlag==1){
                        connStatInfoTable[index]->appFlag=2;
                    }
                    if(edge==0){
                        if(ipv4Hdr->time_to_live<=64){
                            connStatInfoTable[index]->osFlag=ISLINUX;
                        }else if(ipv4Hdr->time_to_live<=128){
                            connStatInfoTable[index]->osFlag=ISWINDOWNS;
                        }else{
                            connStatInfoTable[index]->osFlag=UNKNOWNOS;
                        }
                    }
                }
            }
        }else{
            return 0;
        }
    }else{
        if((tcpHdr->tcp_flags&TCP_FIN_FLAG)==0){
            connStatInfoTable[index]->lastTime=rte_rdtsc();
            connStatInfoTable[index]->totalBytes+=ipv4Hdr->total_length;
            if(connStatInfoTable[index]->appFlag==0){
                if(appFlag==0){
                    connStatInfoTable[index]->appFlag=1;
                }else if(appFlag==1){
                    connStatInfoTable[index]->appFlag=2;
                }
                
            }
            if(connStatInfoTable[index]->osFlag==0){
                if(edge==0){
                    if(ipv4Hdr->time_to_live<=64){
                        connStatInfoTable[index]->osFlag=ISLINUX;
                    }else if(ipv4Hdr->time_to_live<=128){
                        connStatInfoTable[index]->osFlag=ISWINDOWNS;
                    }else{
                        connStatInfoTable[index]->osFlag=UNKNOWNOS;
                    }
                }
            }
        }else{
            index=rte_hash_del_key(connectionHashTable,(const void *)key);
            if(index==-EINVAL){
                printf("invalid parameters in hash delete!\n");
                return -1;
            }else if(index==-ENOENT){
                printf("delete key that does not exist!\n");
                return -3;
            }else{
                connect_statis_info_p pConnStatInfoEntry=connStatInfoTable[index];
                connStatInfoTable[index]=NULL;
                pConnStatInfoEntry->firstTime=0;
                pConnStatInfoEntry->lastTime=0;
                pConnStatInfoEntry->totalBytes=0;
                pConnStatInfoEntry->osFlag=0;
                unusedTail->next=pConnStatInfoEntry;
                unusedTail=unusedTail->next;
            }
        }
    }
    return 0;
}

static inline void
print_ether_addr(const char *what, struct ether_addr *eth_addr)
{
	char buf[ETHER_ADDR_FMT_SIZE];
	ether_format_addr(buf, ETHER_ADDR_FMT_SIZE, eth_addr);
	printf("%s%s", what, buf);
}

static int
main_loop(void *arg)
{
	struct rte_mbuf *mbufs[32];
	struct ether_hdr *eth_hdr;
   	struct ipv4_hdr *ipv4Hdr;
	//struct rte_flow_error error;
	uint16_t nb_rx;
	uint16_t i;
	uint16_t j;

    	unsigned socketid=rte_socket_id();
    	setup_hash(socketid);

	while (!force_quit) {
		for (i = 0; i < nr_queues; i++) {
			nb_rx = rte_eth_rx_burst(port_id,
						i, mbufs, 32);
			if (nb_rx) {
				for (j = 0; j < nb_rx; j++) {
					struct rte_mbuf *m = mbufs[j];

					eth_hdr = rte_pktmbuf_mtod(m,
							struct ether_hdr *);

					if(RTE_ETH_IS_IPV4_HDR(m->packet_type)){
						ipv4Hdr =
						rte_pktmbuf_mtod_offset(m, struct ipv4_hdr *,
							sizeof(struct ether_hdr));
                                              
						ipv4_2tuple key;
						int edgeAndAppFlag,edge,appFlag;
						edgeAndAppFlag=getConnHashKey(ipv4Hdr,&key);
						if(edgeAndAppFlag==UNKNOWN||edgeAndAppFlag==NOTTCP){
							continue;
						}	
						appFlag=(edgeAndAppFlag&0x0000ffff);
						edge=(edgeAndAppFlag>>16);
						int updateRes=updateConnStatInfo(ipv4Hdr,&key,edge,appFlag);
						if(updateRes!=0){
							if(updateRes==-2){
								force_quit=1;
								break;
							}else{
								continue;
							}
						}
					}else{
						rte_pktmbuf_free(m);
					}
				}
			}
		}
	}

	rte_eth_dev_stop(port_id);
	rte_eth_dev_close(port_id);
    	return 0;
}

static void my_rte_delay_s(uint32_t s){
    uint64_t start=rte_get_timer_cycles();
    uint64_t ticks=((uint64_t)s)*rte_get_timer_hz();
    while(((rte_get_timer_cycles()-start)<ticks)&&(!force_quit)){
        rte_pause();
    }
}

static void periodic_scan(void){
    while(!force_quit){
        my_rte_delay_s(SCANINTERVAL);
        if(force_quit) break;
        uint32_t winDevNum=0,linDevNum=0,otherDevNum=0;
        int i;
        for(i=0;i<CON_HASH_ENTRIES;i++){
            connect_statis_info_p pConnStatInfoEntry=connStatInfoTable[i];
            if(pConnStatInfoEntry!=NULL){
                uint64_t ticks=pConnStatInfoEntry->lastTime-pConnStatInfoEntry->firstTime;
                uint32_t duraTime=ticks/rte_get_tsc_hz();
                if(duraTime<VALIDTIMEDURATION){
                    continue;
                }
                if(pConnStatInfoEntry->appFlag==1){
                    if(pConnStatInfoEntry->totalBytes<VALIDSPEEDSFORWECHAT*duraTime){
                        if(pConnStatInfoEntry->osFlag==ISLINUX) linDevNum++;
                        if(pConnStatInfoEntry->osFlag==UNKNOWNOS) otherDevNum++;
                    }
                }else if(pConnStatInfoEntry->appFlag==2){
                    if(pConnStatInfoEntry->totalBytes<VALIDSPEEDSFOR360*duraTime){
                        if(pConnStatInfoEntry->osFlag==ISWINDOWNS) winDevNum++;
                        if(pConnStatInfoEntry->osFlag==UNKNOWNOS) otherDevNum++;
                    }
                }
            }
        }
        time_t now;
        struct tm *tm_now;
        time(&now);
        tm_now=localtime(&now);
        printf("there are %u windows devices,%u linux devices,%u otheros devices at time %d:%d:%d\n",
                winDevNum,linDevNum,otherDevNum,tm_now->tm_hour,tm_now->tm_min,tm_now->tm_sec);
    }
}


static void
assert_link_status(void)
{
	struct rte_eth_link link;
	uint8_t rep_cnt = MAX_REPEAT_TIMES;

	memset(&link, 0, sizeof(link));
	do {
		rte_eth_link_get(port_id, &link);
		if (link.link_status == ETH_LINK_UP)
			break;
		rte_delay_ms(CHECK_INTERVAL);
	} while (--rep_cnt);

	if (link.link_status == ETH_LINK_DOWN)
		rte_exit(EXIT_FAILURE, ":: error: link is still down\n");
}

static void
init_port(void)
{
	int ret;
	uint16_t i;
	struct rte_eth_conf port_conf = {
		.rxmode = {
			.split_hdr_size = 0,
			.ignore_offload_bitfield = 1,
			.offloads = DEV_RX_OFFLOAD_CRC_STRIP,
		},
		.txmode = {
			.offloads =
				DEV_TX_OFFLOAD_VLAN_INSERT |
				DEV_TX_OFFLOAD_IPV4_CKSUM  |
				DEV_TX_OFFLOAD_UDP_CKSUM   |
				DEV_TX_OFFLOAD_TCP_CKSUM   |
				DEV_TX_OFFLOAD_SCTP_CKSUM  |
				DEV_TX_OFFLOAD_TCP_TSO,
		},
	};

	struct rte_eth_txconf txq_conf;
	struct rte_eth_rxconf rxq_conf;
	struct rte_eth_dev_info dev_info;

	printf(":: initializing port: %d\n", port_id);
	ret = rte_eth_dev_configure(port_id,
				nr_queues, nr_queues, &port_conf);
	if (ret < 0) {
		rte_exit(EXIT_FAILURE,
			":: cannot configure device: err=%d, port=%u\n",
			ret, port_id);
	}

	rte_eth_dev_info_get(port_id, &dev_info);
	rxq_conf = dev_info.default_rxconf;
	rxq_conf.offloads = port_conf.rxmode.offloads;
	/* only set Rx queues: something we care only so far */
	for (i = 0; i < nr_queues; i++) {
		ret = rte_eth_rx_queue_setup(port_id, i, 512,
				     rte_eth_dev_socket_id(port_id),
				     &rxq_conf,
				     mbuf_pool);
		if (ret < 0) {
			rte_exit(EXIT_FAILURE,
				":: Rx queue setup failed: err=%d, port=%u\n",
				ret, port_id);
		}
	}

	txq_conf = dev_info.default_txconf;
	txq_conf.offloads = port_conf.txmode.offloads;

	for (i = 0; i < nr_queues; i++) {
		ret = rte_eth_tx_queue_setup(port_id, i, 512,
				rte_eth_dev_socket_id(port_id),
				&txq_conf);
		if (ret < 0) {
			rte_exit(EXIT_FAILURE,
				":: Tx queue setup failed: err=%d, port=%u\n",
				ret, port_id);
		}
	}

	rte_eth_promiscuous_enable(port_id);
	ret = rte_eth_dev_start(port_id);
	if (ret < 0) {
		rte_exit(EXIT_FAILURE,
			"rte_eth_dev_start:err=%d, port=%u\n",
			ret, port_id);
	}

	assert_link_status();

	printf(":: initializing port: %d done\n", port_id);
}

static void
signal_handler(int signum)
{
	if (signum == SIGINT || signum == SIGTERM) {
		printf("\n\nSignal %d received, preparing to exit...\n",
				signum);
		force_quit = true;
	}
}

int
main(int argc, char **argv)
{
    	initConnStatInfoEntries();
    	addAppIpSegment();
	printf("init ok!\n");

	int ret;
	uint16_t nr_ports;

	ret = rte_eal_init(argc, argv);
	if (ret < 0)
		rte_exit(EXIT_FAILURE, ":: invalid EAL arguments\n");

	force_quit = false;
	signal(SIGINT, signal_handler);
	signal(SIGTERM, signal_handler);

	nr_ports = rte_eth_dev_count_avail();
	if (nr_ports == 0)
		rte_exit(EXIT_FAILURE, ":: no Ethernet ports found\n");
	port_id = 0;
	if (nr_ports != 1) {
		printf(":: warn: %d ports detected, but we use only one: port %u\n",
			nr_ports, port_id);
	}
	mbuf_pool = rte_pktmbuf_pool_create("mbuf_pool", 4096, 128, 0,
					    RTE_MBUF_DEFAULT_BUF_SIZE,
					    rte_socket_id());
	if (mbuf_pool == NULL)
		rte_exit(EXIT_FAILURE, "Cannot init mbuf pool\n");

	init_port();

	unsigned lcore_id;
   	RTE_LCORE_FOREACH_SLAVE(lcore_id){
        	rte_eal_remote_launch(main_loop,NULL,lcore_id);
    	}
	periodic_scan();

    	rte_eal_mp_wait_lcore();

	return 0;
}
