/*
 * Spire.
 *
 * The contents of this file are subject to the Spire Open-Source
 * License, Version 1.0 (the ``License''); you may not use
 * this file except in compliance with the License.  You may obtain a
 * copy of the License at:
 *
 * http://www.dsn.jhu.edu/spire/LICENSE.txt
 *
 * or in the file ``LICENSE.txt'' found in this distribution.
 *
 * Software distributed under the License is distributed on an AS IS basis,
 * WITHOUT WARRANTY OF ANY KIND, either express or implied. See the License
 * for the specific language governing rights and limitations under the
 * License.
 *
 * Spire is developed at the Distributed Systems and Networks Lab,
 * Johns Hopkins University and the Resilient Systems and Societies Lab,
 * University of Pittsburgh.
 *
 * Creators:
 *   Yair Amir            yairamir@cs.jhu.edu
 *   Trevor Aron          taron1@cs.jhu.edu
 *   Amy Babay            babay@pitt.edu
 *   Thomas Tantillo      tantillo@cs.jhu.edu
 *   Sahiti Bommareddy    sahiti@cs.jhu.edu
 *   Maher Khan           maherkhan@pitt.edu
 *
 * Major Contributors:
 *   Marco Platania       Contributions to architecture design
 *   Daniel Qian          Contributions to Trip Master and IDS
 *
 * Contributors:
 *   Samuel Beckley       Contributions to HMIs
 *
 * Copyright (c) 2017-2023 Johns Hopkins University.
 * All rights reserved.
 *
 * Partial funding for Spire research was provided by the Defense Advanced
 * Research Projects Agency (DARPA), the Department of Defense (DoD), and the
 * Department of Energy (DoE).
 * Spire is not necessarily endorsed by DARPA, the DoD or the DoE.
 *
 */


#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <netdb.h>
#include <assert.h>
#include <signal.h>
#include <sys/un.h>
#include <sys/stat.h>
#include <errno.h>
#include <arpa/inet.h>

#include "packets.h"
#include "openssl_rsa.h"
#include "net_wrapper.h"
#include "def.h"
#include "data_structs.h"
#include "tc_wrapper.h"

#include "spu_alarm.h"
#include "spu_events.h"
#include "spu_memory.h"
#include "spu_data_link.h"
#include "spines_lib.h"

#define KEY_PAYLOAD_MAXSIZE 40000 

static const sp_time      Repeat_Timeout    = {1, 0};

static int                Ctrl_Spines       = -1;                       /* Spines configuration/control network socket */
static struct sockaddr_in Spines_Conf_Addr;

static int32u             New_Global_Configuration_Number;              /* Identifier for this new configuration */
static signed_message    *Configuration_Message;                        /* The global configuration message to send */

static int                Total_Key_Frags;                              /* Number of key fragments */
static signed_message    *Key_Messages[10];                             /* The Total_Key_Frags key messages to send */

static char               Key_Buff[KEY_PAYLOAD_MAXSIZE];                /* Buffer used for building up key messages */
static int32u             Curr_Idx;                                     /* Used for tracking current location within Key_Buff */

static int                Counter           = 0;                        /* Counts how many times I've broadcast a given configuration */

char conf_dir[100];
extern server_variables    VAR;

void Usage(int argc, char **argv);
void Init_CM_Network();
void generate_keys(int curr_n, int curr_f, int curr_k, char * base_dir);
void construct_keys_messages(int curr_server_count,char *based_dir); 
void new_broadcast_configuration_message(int code, void *dummy);
void repeat_broadcast_configuration_message(int code, void *dummy);

void construct_key_message();
void read_pub_key(const char * filename,int type,int id);
void read_pvt_key(const char * filename,int type,int id);

/**
 * @brief Simple function for opening files and error handling
 * 
 * @param filename name of file
 * @return FILE*
 */
FILE* open_file(const char* filename) {
    FILE* fp = fopen(filename, "r");
    if (!fp) {
        Alarm(EXIT, "Error opening %s\n", filename);
    }
    return fp;
}

/**
 * @brief Insert private key header in `Key_Buff`
 * 
 * @param type key type (e.g. PRIME_RSA_PVT)
 * @param id server id
 * @param keysize size of key
 * @param key_parts number of partitions for key
 * @param enc_key_size size of encrypted key
 */
void fill_pvt_key_header(int type, int id, int keysize, int key_parts, int enc_key_size) {
    pvt_key_header *pvt_header = (pvt_key_header*) &Key_Buff[Curr_Idx];
    pvt_header->key_type = type;
    pvt_header->id = id;
    pvt_header->unenc_size = keysize;
    pvt_header->pvt_key_parts = key_parts;
    pvt_header->pvt_key_part_size = enc_key_size;
    Curr_Idx += sizeof(pvt_key_header);
}

/**
 * @brief Insert public key header in `Key_Buff` 
 * 
 * @param type key type (e.g. PRIME_RSA_PUB)
 * @param id server id
 * @param keysize size of key
 */
void fill_pub_key_header(int type, int id, int keysize) {
    pub_key_header *pub_header = (pub_key_header*) &Key_Buff[Curr_Idx];
    pub_header->id = id;
    pub_header->key_type = type;
    pub_header->size = keysize;
    Curr_Idx += sizeof(pub_key_header);
}

/**
 * @brief Read chunks of data of a specified size from file, encrypt, and store in `Key_Buff`
 * 
 * @param enc_key_filename 
 * @param fp 
 * @param keysize 
 * @param enc_key_size 
 * @param key_parts 
 */
void fill_enc_key_chunks(const char* enc_key_filename, FILE* fp, int keysize, int enc_key_size, int key_parts) {
    int rem_data_len = keysize;
    //int data_len = 0;
    char* enc_buff = malloc(enc_key_size * 2);
    char* data_buff = enc_buff + enc_key_size;

    if (!enc_buff) {
        Alarm(EXIT,"Error allocating dynamic memory for enc_buff\n");
    }

    // Fill encrypted key chunks after header
    for (int j = 0; j < key_parts; j++) {
        memset(enc_buff, 0, enc_key_size * 2);
        // Read from file in chunks
        int chunk_size = (rem_data_len >= enc_key_size) ? enc_key_size : rem_data_len;
        //data_len = chunk_size;
        fread(data_buff, chunk_size, 1, fp);
        rem_data_len -= chunk_size;
        //OPENSSL_RSA_Encrypt(enc_key_filename,data_buff,data_len,enc_buff);
        OPENSSL_RSA_Encrypt(enc_key_filename, data_buff, enc_key_size, enc_buff);
        memcpy(&Key_Buff[Curr_Idx], enc_buff, enc_key_size);
        //memcpy(&Key_Buff[Curr_Idx],data_buff,enc_key_size);
        Curr_Idx += enc_key_size;
    }
}

/**
 * @brief 
 * 
 * @param conf_msg 
 */
void read_conf_def(nm_message* conf_msg) {
    FILE* fp;
    char* param;
    char* value;
    char* line;
    char seps[]  = " ";
    char  filename[200];

    memset(filename, 0, sizeof(filename));
    sprintf(filename, "./%s/conf_def.txt", conf_dir);
    fp = open_file(filename);

    /* Read each line of conf_def.txt file. Each line consists of a string
     * identifying the parameter and an integer representing the parameter
     * value (e.g. "N 6" sets number of servers N to 6) */
    while ((read = getline(&line, &len, fp)) != -1)
    {
        Alarm(DEBUG,"read line is : %s", line);

        /* Get param and value from line */
        param = strtok(line, seps);
        if (!param) Alarm(EXIT, "Invalid conf_def.txt format!");

        value = strtok(NULL, seps);
        if (!value) Alarm(EXIT, "Invalid conf_def.txt format!");

        /* Fill in relevant conf message field based on param */
        if (!strcmp(param,"N")){
            conf_msg->N = atoi(value);
            Alarm(DEBUG,"New N=%u\n",conf_msg->N);
        }
        if (!strcmp(param,"f"))
            conf_msg->f = atoi(value);
        if (!strcmp(param,"k"))
            conf_msg->k = atoi(value);
        if (!strcmp(param,"s"))
            conf_msg->num_sites = atoi(value);
        if (!strcmp(param,"c"))
            conf_msg->num_cc = atoi(value);
        if (!strcmp(param,"d"))
            conf_msg->num_dc = atoi(value);
        if (!strcmp(param,"cr"))
            conf_msg->num_cc_replicas = atoi(value);
        if (!strcmp(param,"dr"))
            conf_msg->num_dc_replicas = atoi(value);
    }

    fclose(fp);

    if (line) {
        free(line);
        line = NULL;
    }
}

/**
 * @brief Read metadata from replicas for new configuration. For example:
 * 
 *     `1 1 aster1 192.168.53.69 192.168.53.69 192.168.53.69 192.168.53.69 1`
 * 
 *     `4 2 aster1 192.168.53.69 192.168.53.69 192.168.53.69 192.168.53.69 1`
 * 
 * @param conf_msg 
 * 
 * @note
 * Expected fields are:
 * 
 * `TPM_ID`   :    Permanent ID associated with replica TPM
 * 
 * `Local_ID` :    ID for this specific configuration (in the second example
 *                   line, replica with TPM_ID 4 is acting as replica 2 in
 *                   the new configuration). Local_IDs are typically the
 *                   same as TPM_IDs in the original "maximal"
 *                   configuration, but may change when reconfiguring to a
 *                   smaller configuration
 * 
 * `Machine_Name`
 * 
 * `Spines External IP`
 * 
 * `Spines Internal IP`
 * 
 * `Prime IP`
 * 
 * `DC_CC_Flag` :  1 == control center (CC), 0 == data center (DC)
 * 
 */
void read_new_conf(nm_message* conf_msg) {
    FILE* fp;
    char* line;
    char  filename[200];
    size_t len = 0;
    ssize_t read;

    /**** Start Filling in IPs and Ports in config_message by reading from conf_dir/new_conf.txt file ****/
    // Open new_conf.txt file
    memset(filename,0,sizeof(filename));
    sprintf(filename,"./%s/new_conf.txt",conf_dir);
    Alarm(DEBUG,"Opening %s\n",filename);
    fp = open_file(filename);

    while ((read = getline(&line, &len, fp)) != -1)
    {
        /* Read data from file line */
        const char* t_id      = strtok(line, " ");
        int tpm_id_curr       = atoi(t_id);

        const char* l_id      = strtok(NULL, " ");
        int local_id_curr     = atoi(l_id);

        const char* m_name    = strtok(NULL, " ");
        const char* sp_ext_ip = strtok(NULL, " ");
        const char* sp_int_ip = strtok(NULL, " ");
        const char* sm_ip     = strtok(NULL, " ");
        const char* prime_ip  = strtok(NULL, " ");
        const char* flag      = strtok(NULL, " ");
        int dc_cc_flag        = atoi(flag);        /* 1 == control center (CC), 0 == data center (DC) */

        /* Fill in message fields based on file data */
        conf_msg->tpm_based_id[tpm_id_curr-1] = local_id_curr;
        conf_msg->replica_flag[tpm_id_curr-1] = dc_cc_flag;
        sprintf(conf_msg->sm_addresses[tpm_id_curr-1], "%s", sm_ip);
        sprintf(conf_msg->spines_ext_addresses[tpm_id_curr-1], "%s", sp_ext_ip);
        sprintf(conf_msg->spines_int_addresses[tpm_id_curr-1], "%s", sp_int_ip);
        sprintf(conf_msg->prime_addresses[tpm_id_curr-1], "%s", prime_ip);

        Alarm(PRINT, "t_id=%d , l_id=%d, sm_ip=%s\n", tpm_id_curr-1,
              conf_msg->tpm_based_id[tpm_id_curr-1],
              conf_msg->spines_ext_addresses[tpm_id_curr-1]);
    }
    conf_msg->spines_ext_port = SPINES_EXT_PORT;
    // Is this an error???
    conf_msg->spines_ext_port = SPINES_PORT;

    fclose(fp);

    if (line){
        free(line);
        line = NULL;
	}
}

/**
 * @brief Generate RSA keys for configuration manager and store at `base_dir`
 * 
 * @param curr_n: scada configuration (e.g. `curr_n = 18` => 6+6+6)
 * @param curr_f: number of failures
 * @param curr_k: number of proactive recoveries
 * @param base_dir: location of newly generated keys 
 */
void generate_keys(int curr_n, int curr_f, int curr_k, char * base_dir)
{
    char sm_keys_dir[100];
    char prime_keys_dir[100];
    struct stat st = {0};

    // Set up SCADA Master (sm) and Prime key directory names
    memset(sm_keys_dir, 0, sizeof(sm_keys_dir));
    memset(prime_keys_dir, 0, sizeof(prime_keys_dir));

    sprintf(sm_keys_dir, "./%s/keys", base_dir);
    sprintf(prime_keys_dir, "./%s/prime_keys", base_dir);
    
    // If directories do not already exist, create them
    if (stat(sm_keys_dir, &st) == -1) {
        if (mkdir(sm_keys_dir, 0755) < 0) 
            Alarm(EXIT, "Error creating %s\n", sm_keys_dir);
	}
    if (stat(prime_keys_dir, &st) == -1) {
        if (mkdir(prime_keys_dir, 0755) < 0)
            Alarm(EXIT, "Error creating %s\n", prime_keys_dir);
    }

    // Generate keys
    TC_with_args_Generate(curr_f + 1, sm_keys_dir, curr_f, curr_k, 1);
    TC_with_args_Generate(curr_f + 1, prime_keys_dir, curr_f, curr_k, 1);
    OPENSSL_RSA_Generate_Keys_with_args(curr_n, prime_keys_dir);
}

/**
 * @brief Logs and creates new message of keys
 * 
 */
void finalize_message() {
    Alarm(DEBUG,"One key payload ready\n");
    construct_key_message();
    fflush(stdout);    
}

/**
 * @brief 
 * 
 */
void construct_key_message() {
    signed_message* pkt_header;
    key_msg_header* km_header;
    char* new_keys;
    size_t message_size;

    Alarm(DEBUG, "construct_key_message() called for Total_Key_Frags = %d\n",
          Total_Key_Frags);
    /* Call malloc() once and use pointer arithmetic to partition pkt_header,
     * key header, and keys */
    message_size = sizeof(signed_message) + sizeof(key_msg_header) +
                   (Curr_Idx * sizeof(char));
    Key_Messages[Total_Key_Frags] = (signed_message*) malloc(message_size);

    // Insert metadata into message header. `len` represents 
    pkt_header = Key_Messages[Total_Key_Frags];
    memset(pkt_header, 0, message_size);

    pkt_header->machine_id = 0;
    pkt_header->len = sizeof(key_msg_header) + Curr_Idx;
    pkt_header->global_configuration_number = New_Global_Configuration_Number;
    pkt_header->type = CONFIG_KEYS_MSG;

    // Partition headers and insert number of key fragments into key header
    km_header = (key_msg_header*) (pkt_header + 1);
    km_header->frag_idx = ++Total_Key_Frags;

    new_keys = (char*)(km_header + 1);
    memcpy(new_keys, Key_Buff, Curr_Idx * sizeof(char));

    // Sign message
    OPENSSL_RSA_Sign(((byte*)pkt_header) + SIGNATURE_SIZE,
                     sizeof(signed_message) + pkt_header->len - SIGNATURE_SIZE,
                     (byte*)pkt_header);

    // Reset Key Buffer
    memset(Key_Buff, 0, KEY_PAYLOAD_MAXSIZE);
    Curr_Idx = 0;

    Alarm(DEBUG, "Post construct_key_message now Total_Key_Frags = %d\n",
          Total_Key_Frags);
}


void read_pub_key(const char * filename, int type, int id){
    int keysize = 0;
    FILE* fp = open_file(filename);

    // Get key size
    keysize = getFileSize(filename);
    Alarm(DEBUG, "%s keysize=%d\n", filename, keysize);

    /* Key can't fit in current message we are constructing (it is "full"), so
     * finalize and store the current message */
    if (Curr_Idx + sizeof(pub_key_header) + keysize >= KEY_PAYLOAD_MAXSIZE) {
        finalize_message();
    }

    // Fill in public key header
    fill_pub_key_header(pub_header, type, id, keysize);

    // Store public key into buffer
    fread(&Key_Buff[Curr_Idx], keysize, 1, fp);
    Curr_Idx += keysize;

    fclose(fp);

    Alarm(PRINT,"after pubkey Curr_Idx=%d, header=%d, keysize=%d\n", 
          Curr_Idx, sizeof(pub_key_header), keysize);
}

void read_pvt_key(const char * filename, int type, int id) {
    FILE* fp;
    char enc_key_filename[250];
    int keysize, enc_key_size, key_parts;

    //Get enc key size, pvt key and cal parts to enc 
    memset(enc_key_filename, 0, sizeof(enc_key_filename));
	sprintf(enc_key_filename, "./tpm_keys/tpm_public%d.pem", id + (type != PRIME_RSA_PVT) ? 1 : 0);

    enc_key_size = OPENSSL_RSA_Get_KeySize(enc_key_filename);

    fp = open_file(filename);

    keysize = getFileSize(filename);
    Alarm(DEBUG, "%s keysize=%d\n", filename, keysize);

    key_parts = (int) keysize / enc_key_size;
    if(keysize % enc_key_size > 0)
        key_parts += 1;
    
    //Alarm(DEBUG, "%s keysize=%d, enc_key_size=%d, parts=%d\n",filename,keysize,enc_key_size,key_parts);
      
    /* Key can't fit in current message we are constructing (it is "full"), so
     * finalize and store the current message */
    if(Curr_Idx + sizeof(pvt_key_header) + (key_parts * enc_key_size) >= KEY_PAYLOAD_MAXSIZE){
        finalize_message();
    }

    // Construct pvt_key_header
    fill_pvt_key_header(type, id, keysize, key_parts, enc_key_size);
   //fread(&Key_Buff[Curr_Idx], keysize,1,fp);
   // Encrypt
    fill_enc_key_chunks(enc_key_filename, keysize, enc_key_size, key_parts);
    
    fclose(fp);
    Alarm(PRINT, "after %s pvtkey Curr_Idx=%d, header=%d, keysize=%d\n", filename,
          Curr_Idx, sizeof(pvt_key_header), (key_parts * enc_key_size));
    
}

/**
 * @brief Read all keys into Key_Buf, Creating and storing key fragments as they "fill up"
 * 
 * @param curr_server_count number of servers in new configuration
 * @param base_dir directory containing public/private
 */
void construct_keys_messages(int curr_server_count,char *base_dir)
{
    char filename[100];

    //sm_tc_pub
    memset(filename,0,sizeof(filename));
    sprintf(filename, "./%s/keys/pubkey_1.pem", base_dir);
    Alarm(PRINT,"start before sm_tc_pub Curr_Idx=%d\n",Curr_Idx);
    read_pub_key(filename, SM_TC_PUB, 1);

    //prime_tc_pub
    memset(filename,0,sizeof(filename));
    sprintf(filename, "./%s/prime_keys/pubkey_1.pem", base_dir);
    Alarm(PRINT,"start before prime_tc_pub Curr_Idx=%d\n",Curr_Idx);
    read_pub_key(filename, PRIME_TC_PUB, 1);

    //prime_rsa_pub
    for(int i=1; i<= curr_server_count; i++){
    	Alarm(PRINT,"start before prime_rsa_pub Curr_Idx=%d\n",i);
        memset(filename,0,sizeof(filename));
        sprintf(filename, "./%s/prime_keys/public_%02d.key", base_dir, i);
        read_pub_key(filename, PRIME_RSA_PUB, i);
    } 

    //sm_tc_shares
    for(int i=0; i < curr_server_count; i++){
    	Alarm(PRINT,"start before sm_tc_shares Curr_Idx=%d\n",i);
        memset(filename,0,sizeof(filename));
        sprintf(filename, "./%s/keys/share%d_1.pem", base_dir, i);
        read_pvt_key(filename, SM_TC_PVT, i);
    }

    //prime_tc_shares
    for(int i=0; i < curr_server_count; i++){
    	Alarm(PRINT,"start before prime_tc_shares Curr_Idx=%d\n",i);
        memset(filename,0,sizeof(filename));
        sprintf(filename, "./%s/prime_keys/share%d_1.pem", base_dir, i);
        read_pvt_key(filename, PRIME_TC_PVT, i);
    }

    //prime_rsa_pvt
    for(int i=1; i <= curr_server_count; i++){
    	Alarm(PRINT,"start before prime_rsa_pvt Curr_Idx=%d\n",i);
        memset(filename,0,sizeof(filename));
        sprintf(filename, "./%s/prime_keys/private_%02d.key", base_dir, i);
        read_pvt_key(filename, PRIME_RSA_PVT, i);
    }

    /* "Flush" final key message (which may not be completely filled */
    if (Curr_Idx > 0) {
        Alarm(DEBUG,"After key constructs , key+buff has content\n");
        construct_key_message(); 
    }
} 

int main(int argc, char **argv)
{
    setlinebuf(stdout);
    Alarm_set_types(PRINT);
    //Alarm_set_types(STATUS|DEBUG);

    // Verify correct argument usage
    Usage(argc, argv);

    // Initialize new RSA generator
    OPENSSL_RSA_Init();
    OPENSSL_RSA_Read_Keys(0,RSA_CONFIG_MNGR,"./keys");

    Init_CM_Network();

    // Initialize Event Handler
    E_init();
    // Queue up action to create new configuration and propagate across Spines network
    E_queue(new_broadcast_configuration_message, NULL, NULL, Repeat_Timeout);
    E_handle_events(); 
}

void Usage(int argc, char**argv)
{
    VAR.Num_Servers = (3*NUM_F) + (2*NUM_K) + 1;

    if(argc < 2){
        Alarm(EXIT, "Usage: %s configuration_dir_path\n", argv[0]);
    }

    memset(conf_dir, 0, 100);
    sprintf(conf_dir, "%s", argv[1]);
}

void Init_CM_Network()
{
    int ttl = 255;
    struct hostent h_ent;

    // Create Spines socket
    Ctrl_Spines = Spines_Mcast_SendOnly_Sock(CONF_MNGR_ADDR, CONFIGUATION_SPINES_PORT, SPINES_PRIORITY);
    if (Ctrl_Spines < 0 ) {
        /* TODO try reconnecting? */
        Alarm(EXIT, "Error setting up control spines network, exiting\n");
    }

    // Initialize Spines multicast address
    memcpy(&h_ent, gethostbyname(CONF_SPINES_MCAST_ADDR), sizeof(h_ent));
    memcpy(&Spines_Conf_Addr.sin_addr, h_ent.h_addr, sizeof(Spines_Conf_Addr.sin_addr));
    // Store Transmission protocol and port
    Spines_Conf_Addr.sin_family = AF_INET;
    Spines_Conf_Addr.sin_port   = htons(CONF_SPINES_MCAST_PORT);
    if(spines_setsockopt(Ctrl_Spines, 0, SPINES_IP_MULTICAST_TTL, &ttl, sizeof(ttl)) != 0) {
        Alarm(EXIT, "Spines setsockopt error\n");
    }

    Alarm(PRINT,"MCAST set up done\n");
}

void new_broadcast_configuration_message(int code, void *dummy)
{
    nm_message *conf_msg;
    char filename[200];
    FILE * fp;
    char * line = NULL;
    size_t len = 0;
    ssize_t read;
    char seps[]  = " ";
    char *param;
    char *value;
    sp_time now;
    
    Total_Key_Frags = 0;
    memset(Key_Buff, 0, KEY_PAYLOAD_MAXSIZE);
    Curr_Idx = 0;

    Alarm(DEBUG,"New Config Msg\n");

    /* Get global configuration number based on current time (limited to 1 reconf per sec) */
    now = E_get_time();
    New_Global_Configuration_Number = now.sec;

    /* Allocate buffer for the new message: signed_message header + nm_message */
    Configuration_Message = (signed_message*) malloc(sizeof(signed_message) + sizeof(nm_message));
    memset(Configuration_Message, 0, sizeof(signed_message) + sizeof(nm_message)); 

    // Fill in signed message header
    Configuration_Message->machine_id = 0;
    Configuration_Message->len = sizeof(nm_message);
    Configuration_Message->type = CLIENT_OOB_CONFIG_MSG;
    Configuration_Message->global_configuration_number = New_Global_Configuration_Number;

    /* Start filling in config_message by reading config defines from 
     * conf_dir/conf_def.txt */
    conf_msg = (nm_message *)(Configuration_Message + 1);

    // Open conf_def.txt file
    read_conf_def(conf_msg);

    Alarm(DEBUG,"N=%u, f=%u, k=%u, s=%u\n",conf_msg->N,conf_msg->f,conf_msg->k,conf_msg->num_sites); 
    /**** End filling in config_message by reading config defines from conf_dir/conf_def.txt ****/

    /* Generate keys for the new configuration, based on parameters above and
     * write them to files in conf_dir */
    generate_keys(conf_msg->N, conf_msg->f, conf_msg->k, conf_dir);

    /*Compose seperate conf_key_messages, sign and store them for repeat broadcast*/ 
   
    /* We will construct config_keys messages and fill the fragments count into config_message*/ 
    construct_keys_messages(conf_msg->N, conf_dir); 
	
    conf_msg->frag_num = Total_Key_Frags; 
    read_new_conf(conf_msg);
   
    Alarm(DEBUG, "Composed Configuration Message of len=%u\n",Configuration_Message->len);

    /* Sign message */
    OPENSSL_RSA_Sign( ((byte*)Configuration_Message) + SIGNATURE_SIZE,
                      sizeof(signed_message) + Configuration_Message->len - SIGNATURE_SIZE,
                      (byte*)Configuration_Message );
    
    Alarm(DEBUG, "Composed Configuration Message of len=%u\n",Configuration_Message->len);

    /* Send the message on the configuration network */
    Counter = 0;
    repeat_broadcast_configuration_message(0, NULL);
}

void repeat_broadcast_configuration_message(int code, void *dummy)
{
    int ret = 0;
    int num_bytes = 0;

    /* Broadcast config_message */
    num_bytes = sizeof(signed_message)+Configuration_Message->len;
    ret = spines_sendto(Ctrl_Spines, Configuration_Message, num_bytes, 0, (struct sockaddr *)&Spines_Conf_Addr, sizeof(struct sockaddr)); 
    if(ret != num_bytes){
        Alarm(EXIT,"Control manager: Spines sendto ret != message size\n");
    }
    Alarm(DEBUG,"$$$$Config Manager %d: sent conf message %d bytes to Spines_Conf_Addr addr=%s\n",Counter,num_bytes,inet_ntoa(Spines_Conf_Addr.sin_addr));

    /* Broadcast Key_Messages */
    for(int i = 0; i < Total_Key_Frags; i++){
        num_bytes = sizeof(signed_message)+Key_Messages[i]->len;

        ret = spines_sendto(Ctrl_Spines, Key_Messages[i], num_bytes, 0, (struct sockaddr *)&Spines_Conf_Addr, sizeof(struct sockaddr)); 
        if(ret!=num_bytes){
            Alarm(EXIT,"****Control manager: Spines sendto ret != keys message size\n");
        }
        Alarm(DEBUG,"****Config Manager %d: sent key message %d bytes to Spines_Conf_Addr addr=%s\n",Counter,num_bytes,inet_ntoa(Spines_Conf_Addr.sin_addr));
    }

    Counter += 1;
    
    /* Schedule this function to be called again after Repeat_Timeout */
    E_queue(repeat_broadcast_configuration_message, 0, NULL, Repeat_Timeout);
}
