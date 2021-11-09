#include "rr_idiag.h"
#include "adm_typedefs.h"
#include "adm_string.h"
#include "adm_memory.h"
#include "adm_debug.h"
#include "adm_eCode.h"
#include "adm_tool.h"
#include "adm_security.h"
#include "adm_https.h"
#include "adm_md.h"
#include "adm_config.h"
#include "adm_workqueue.h"
#include "adm_rdc_core.h"
#include "adm_rdc_reportDownload.h"
#include "adm_rdc_reportLog.h"
#include "adm_rdc_taskCheck.h"
#include "adm_rdc_taskInfo.h"
#include "adm_sdkVersion.h"
#include "adm_rdc_cert.h"


#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
#include <unistd.h>
#include <sys/statfs.h>

#include <pthread.h>


static D8U kRRDiagEcodeSuccess = 0x1;
static D8U kRRDiagEcodeFailed = 0x0;
static D8U kRRDiagEcodeTimeout = 0x2;

static D8U kInitOk = 0;


static D32U monotonicSecondTimeGet() {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    D32U tv_sec = ts.tv_sec;
    return tv_sec;
}

static D32U timeoutCalculate(D32U monotonicSecondEndTime) {
    D32U timeout = 0;
    D32U curTime = monotonicSecondTimeGet();
    if (monotonicSecondEndTime > curTime) {
        timeout = monotonicSecondEndTime - curTime;
    } else {
        log_w("monotonicSecondEndTime:%u curTime:%u", monotonicSecondEndTime, curTime);
    }
    return timeout;
}

static D32S rdcTaskTitleListNew(ADM_RDS_Task_T tasks[], int tasksLen, ADM_RDC_TaskTitle_T **taskTitles) {
    D32S ttsLen = 0;
    ADM_RDC_TaskTitle_T *tts = (ADM_RDC_TaskTitle_T *)adm_malloc(tasksLen * sizeof(ADM_RDC_TaskTitle_T));
    if (tts == NULL) {
        log_w("malloc error");
    } else {
        adm_memset(tts, 0x00, tasksLen * sizeof(ADM_RDC_TaskTitle_T));
        ttsLen = tasksLen;
        *taskTitles = tts;
        for (D32S i = 0; i < tasksLen; ++i) {
            tts[i].taskId = tasks[i].taskId;
            tts[i].taskVersion = tasks[i].taskVersion;
        }
    }
    return ttsLen;
}
static void rdcTaskTitleListDel(ADM_RDC_TaskTitle_T taskTitles[], D32S taskTitlesLen) {
    adm_free(taskTitles);
}

static void rdsTaskInfoInit(ADM_RDS_TaskInfo_T *rdsTaskInfo, ADM_RDC_TaskInfo_T *rdcTaskInfo) {
    ADM_RDC_TaskInfo_T *rdc = rdcTaskInfo;
    ADM_RDS_TaskInfo_T *rds = rdsTaskInfo;

    adm_memset(rds, 0x00, sizeof(ADM_RDS_TaskInfo_T));

    rds->sessionId = NULL;
    rds->sessionIdlength = 0;
    if (rdc->sessionId) {
        rds->sessionId = strdup(rdc->sessionId);
        if (rds->sessionId) {
            rds->sessionIdlength = strlen(rds->sessionId);
        }
    }

    rds->taskId = rdc->taskId;
    rds->taskVersion = rdc->taskVersion;
    rds->RetrydiagnoseTimes = rdc->taskInfo.systemParamter.retrydiagnoseTime;

    rds->action = ADM_RDS_TaskInfo_T::ACTION_TASK_ADD;
    if (rdc->isDelete == 0) {
    } else if (rdc->isDelete == 1) {
        rds->action = ADM_RDS_TaskInfo_T::ACTION_TASK_DEL;
    }

    rds->saUrl = NULL;
    rds->saURLlength = 0;
    if (rdc->taskInfo.systemParamter.SAurl) {
        rds->saUrl = strdup(rdc->taskInfo.systemParamter.SAurl);
        if (rds->saUrl) {
            rds->saURLlength = strlen(rds->saUrl);
        }
    }

    rds->type = ADM_RDS_TaskInfo_T::DIAGNOSE_TYPE_SILENCE;
    if (rdc->taskInfo.diagnoseType == 1) {
        rds->type = ADM_RDS_TaskInfo_T::DIAGNOSE_TYPE_NONSILENCE;
    } else if (rdc->taskInfo.diagnoseType == 2) {
    }

    rds->taskType = ADM_RDS_TaskInfo_T::TASK_TYPE_ONCE;
    if (rdc->taskInfo.taskType == 1) {
        rds->taskType = ADM_RDS_TaskInfo_T::TASK_TYPE_CYCLE;
    } else if (rdc->taskInfo.taskType == 2) {
        rds->taskType = ADM_RDS_TaskInfo_T::TASK_TYPE_EVENT;
    } else if (rdc->taskInfo.taskType == 3) {
    }

    rds->executeIncident = 0XFFFF /*product manager*/;
    rds->taskEndTime = (unsigned long)rdc->diagnosisEndTime;
    rds->executeIntervl = rdc->taskInfo.diagnoseConfig.executeInterval;
    rds->executeNumber = rdc->taskInfo.diagnoseConfig.executeNumber;
    rds->Scriptnum = 0;
    rds->scriptinfo = NULL;
    if (rdc->taskInfo.ecus && (rdc->taskInfo.ecusLen > 0)) {
        rds->scriptinfo = (RDS_scriptInfos *)adm_malloc(rdc->taskInfo.ecusLen * sizeof(RDS_scriptInfos));
        if (rds->scriptinfo == NULL) {
            log_w("malloc error");
        } else {
            adm_memset(rds->scriptinfo, 0x00, rdc->taskInfo.ecusLen * sizeof(RDS_scriptInfos));
            rds->Scriptnum = rdc->taskInfo.ecusLen;

            for (D32S j = 0; j < rdc->taskInfo.ecusLen; ++j) {
                rds->scriptinfo[j].scriptId = rdc->taskInfo.ecus[j].scriptId;
                rds->scriptinfo[j].scriptHash = NULL;
                rds->scriptinfo[j].scriptSize = 0;
                rds->scriptinfo[j].scriptPath = NULL;
                rds->scriptinfo[j].scriptpathlength = 0;
                rds->scriptinfo[j].scriptName = NULL;
                rds->scriptinfo[j].scriptNamelength = 0;
                rds->scriptinfo[j].diagnosticaddress = rdc->taskInfo.ecus[j].sourceId;
                rds->scriptinfo[j].busType = rdc->taskInfo.ecus[j].busType;

                if (rdc->taskInfo.scriptInfo && (rdc->taskInfo.scriptInfoLen > 0)) {
                    for (D32S k = 0; k < rdc->taskInfo.scriptInfoLen; ++k) {
                        if (rdc->taskInfo.ecus[j].scriptId == rdc->taskInfo.scriptInfo[k].scriptId) {
                            if (rdc->taskInfo.scriptInfo[k].scriptHash) {
                                rds->scriptinfo[j].scriptHash = strdup(rdc->taskInfo.scriptInfo[k].scriptHash);
                            }
                            rds->scriptinfo[j].scriptSize = rdc->taskInfo.scriptInfo[k].scriptSize;
                            if (rdc->taskInfo.scriptInfo[k].scriptPath /*TODO host path*/) {
                                rds->scriptinfo[j].scriptPath = strdup(rdc->taskInfo.scriptInfo[k].scriptPath);
                                if (rds->scriptinfo[j].scriptPath) {
                                    rds->scriptinfo[j].scriptpathlength = strlen(rds->scriptinfo[j].scriptPath);
                                }
                            }
                            if (rdc->taskInfo.scriptInfo[k].scriptName) {
                                rds->scriptinfo[j].scriptName = strdup(rdc->taskInfo.scriptInfo[k].scriptName);
                                if (rds->scriptinfo[j].scriptName) {
                                    rds->scriptinfo[j].scriptNamelength = strlen(rds->scriptinfo[j].scriptName);
                                }
                            }
                            break;
                        }
                    }
                }
            }
        }
    }

    rds->Triggercondition = ADM_RDS_TaskInfo_T::InvalidData;
    rds->ParameterM = 0XFFFF;
    rds->ParameterN = 0XFFFF;
    if (rdc->taskInfo.diagnoseConfig.triggerCondition == 1) {
        rds->Triggercondition = ADM_RDS_TaskInfo_T::SignalmorethanM;
        rds->ParameterM = rdc->taskInfo.diagnoseConfig.triggerValueM;
    } else if (rdc->taskInfo.diagnoseConfig.triggerCondition == 2) {
        rds->Triggercondition = ADM_RDS_TaskInfo_T::SignallessthanN;
        rds->ParameterN = rdc->taskInfo.diagnoseConfig.triggerValueM;
    } else if (rdc->taskInfo.diagnoseConfig.triggerCondition == 3) {
        rds->Triggercondition = ADM_RDS_TaskInfo_T::eqcondition;
        rds->ParameterM = rdc->taskInfo.diagnoseConfig.triggerValueM;
        rds->ParameterN = rdc->taskInfo.diagnoseConfig.triggerValueN;
    }

    rds->signalid = rdc->taskInfo.diagnoseConfig.triggerSignal;
    rds->executeEnable = rdc->executeEnable;

}
static void rdsTaskInfoDeInit(ADM_RDS_TaskInfo_T *rdsTaskInfo) {
    ADM_RDS_TaskInfo_T *rds = rdsTaskInfo;
    if (rds->sessionId) {
        adm_free(rds->sessionId);
    }
    if (rds->scriptinfo) {
        for (D32S i = 0; i < rds->Scriptnum; ++i) {
            if (rds->scriptinfo[i].scriptHash) {
                adm_free(rds->scriptinfo[i].scriptHash);
            }
            if (rds->scriptinfo[i].scriptPath) {
                adm_free(rds->scriptinfo[i].scriptPath);
            }
            if (rds->scriptinfo[i].scriptName) {
                adm_free(rds->scriptinfo[i].scriptName);
            }
        }
        adm_free(rds->scriptinfo);
    }
}
static void rdsTaskInfoShow(ADM_RDS_TaskInfo_T *rdsTaskInfo) {
    ADM_RDS_TaskInfo_T *rds = rdsTaskInfo;
    log_d(
        "sessionId:%s sessionIdlength:%u taskId:%lu taskVersion:%lu RetrydiagnoseTimes:%u executeEnable:%u action:%d saUrl:%s "
        "saURLlength:%u type:%d taskType:%d executeIncident:%lu taskEndTime:%lld executeIntervl:%lu executeNumber:%u "
        "Scriptnum:%u Triggercondition:%d signalid:%lu ParameterM:%u ParameterN:%u",
        rds->sessionId ? rds->sessionId : "null",
        rds->sessionIdlength,
        rds->taskId,
        rds->taskVersion,
        rds->RetrydiagnoseTimes,
        rds->executeEnable,
        rds->action,
        rds->saUrl ? rds->saUrl : "null",
        rds->saURLlength,
        rds->type,
        rds->taskType,
        rds->executeIncident,
        rds->taskEndTime,
        rds->executeIntervl,
        rds->executeNumber,
        rds->Scriptnum,
        rds->Triggercondition,
        rds->signalid,
        rds->ParameterM,
        rds->ParameterN);
    if (rds->scriptinfo) {
        for (D32S i = 0; i < rds->Scriptnum; ++i) {
            log_d(
                "index:%d scriptId:%u scriptHash:%s scriptSize:%u scriptPath:%s scriptpathlength:%u scriptName:%s "
                "scriptNamelength:%u diagnosticaddress:%u busType:%u",
                i,
                rds->scriptinfo[i].scriptId,
                rds->scriptinfo[i].scriptHash ? rds->scriptinfo[i].scriptHash : "null",
                rds->scriptinfo[i].scriptSize,
                rds->scriptinfo[i].scriptPath ? rds->scriptinfo[i].scriptPath : "null",
                rds->scriptinfo[i].scriptpathlength,
                rds->scriptinfo[i].scriptName ? rds->scriptinfo[i].scriptName : "null",
                rds->scriptinfo[i].scriptNamelength,
                rds->scriptinfo[i].diagnosticaddress,
                rds->scriptinfo[i].busType);
        }
    }
}

static void rdsTaskInit(ADM_RDS_Task_T *task) {
    task->sessionId = NULL;
    task->sessionIdlength = 0;
    task->taskId = 0;
    task->taskVersion = 0;
}
static void rdsTaskDeInit(ADM_RDS_Task_T *task) {
    if (task->sessionId) {
        free(task->sessionId);
    }
}

static void rdsTaskClone(ADM_RDS_Task_T *src, ADM_RDS_Task_T *dst) {
    if (src->sessionId) {
        dst->sessionId = strdup(src->sessionId);
    }

    dst->sessionIdlength = src->sessionIdlength;
    dst->taskId = src->taskId;
    dst->taskVersion = src->taskVersion;
}

#if 0
static void rdcTaskInit(ADM_RDC_Task_T *task) {
    task->taskId = 0;
    task->taskVersion = 0;
}
static void rdcTaskDeInit(ADM_RDC_Task_T *task) {
}
static void rdcTaskClone(ADM_RDC_Task_T *src, ADM_RDC_Task_T *dst) {
    dst->taskId = src->taskId;
    dst->taskVersion = src->taskVersion;
}
#endif

static void rdsUploadLogInfoInit(RDS_uploadloginfo *upload) {
    upload->sessionId = NULL;
    upload->sessionIdlength = 0;
    upload->executeStartTime = 0;
    upload->taskId = 0;
    upload->taskVersion = 0;
    upload->executeEndTime = 0;
    upload->fileType = ADM_RDS_ReportLogFileType_Diagnostic;
    upload->uploadFile = NULL;
    upload->count = 0;
    upload->timestamp = 0;
    upload->uploaddirectory = NULL;
}

static void rdsUploadLogInfoDeInit(RDS_uploadloginfo *upload) {
   
    if (upload->sessionId) {
        free(upload->sessionId);
    }
    if (upload->uploadFile) {
        free(upload->uploadFile);
    }
    if (upload->uploaddirectory) {
        free(upload->uploaddirectory);
    }
}

static void rdsUploadLogInfoClone(RDS_uploadloginfo *src, RDS_uploadloginfo *dst) {
    if (src->sessionId) {
        dst->sessionId = strdup(src->sessionId);
    }

    dst->sessionIdlength = src->sessionIdlength;
    dst->executeStartTime = src->executeStartTime;

    dst->taskId = src->taskId;
    dst->taskVersion = src->taskVersion;
    dst->executeEndTime = src->executeEndTime;
    dst->fileType = src->fileType;
    if (src->uploadFile) {
        dst->uploadFile = strdup(src->uploadFile);
    }
    dst->count = src->count;
    dst->timestamp = src->timestamp;
    if (src->uploaddirectory) {
        dst->uploaddirectory = strdup(src->uploaddirectory);
    }
}

typedef struct {
    DCHAR *backofficeaddress;
    ADM_RDS_Response_F response;
    DCHAR *vin;
    D64S timestamp;
} ADM_RR_IdiagWorkerVinRegisterData_T;

static ADM_RR_IdiagWorkerVinRegisterData_T *rrIdiagWorkerVinRegisterDataNew(DCHAR *backofficeaddress,
                                                                            ADM_RDS_Response_F response,
                                                                            DCHAR *vin,
                                                                            D64S timestamp) {
    ADM_RR_IdiagWorkerVinRegisterData_T *data
        = (ADM_RR_IdiagWorkerVinRegisterData_T *)malloc(sizeof(ADM_RR_IdiagWorkerVinRegisterData_T));
    if (data == NULL) {
        log_w("malloc error");
    } else {
        if (backofficeaddress) {
            data->backofficeaddress = strdup(backofficeaddress);
        } else {
            data->backofficeaddress = NULL;
        }
        data->response = response;
        if (vin) {
            data->vin = strdup(vin);
        } else {
            data->vin = NULL;
        }
        data->timestamp = timestamp;
    }
    return data;
}

static void rrIdiagWorkerVinRegisterDataDel(ADM_RR_IdiagWorkerVinRegisterData_T *data) {
    if (data->backofficeaddress) {
        free(data->backofficeaddress);
    }
    if (data->vin) {
        free(data->vin);
    }

    free(data);
}

typedef struct {
    DCHAR *backofficeaddress;
    ADM_RDS_Response_F response;
    ADM_RDS_Task_T *tasks;
    D32S tasksLen;
    DCHAR *directory;
    //ADM_RDS_Response_timeout timeoutfunction;
    D32U monotonicSecondEndTime;
    DCHAR *cacertPath;
} ADM_RR_IdiagWorkerTaskDownloadData_T;
static ADM_RR_IdiagWorkerTaskDownloadData_T *rrIdiagWorkerTaskDownloadDataNew(char *backofficeaddress,
                                                                              ADM_RDS_Response_F response,
                                                                              ADM_RDS_Task_T tasks[],
                                                                              int tasksLen,
                                                                              char *directory,
                                                                              D32U timeout,
                                                                              DCHAR *cacertPath) {
    ADM_RR_IdiagWorkerTaskDownloadData_T *data
        = (ADM_RR_IdiagWorkerTaskDownloadData_T *)malloc(sizeof(ADM_RR_IdiagWorkerTaskDownloadData_T));
    if (data == NULL) {
        log_w("malloc error");
    } else {
        if (backofficeaddress) {
            data->backofficeaddress = strdup(backofficeaddress);
        } else {
            data->backofficeaddress = NULL;
        }
        data->response = response;
        if (tasks && (tasksLen > 0)) {
            data->tasks = (ADM_RDS_Task_T *)malloc(tasksLen * sizeof(*(data->tasks)));
            if (data->tasks == NULL) {
                log_w("malloc error");
            } else {
                data->tasksLen = tasksLen;
                for (D32S i = 0; i < tasksLen; ++i) {
                    rdsTaskInit(data->tasks + i);
                    rdsTaskClone(tasks + i, data->tasks + i);
                }
            }
        } else {
            data->tasks = NULL;
            data->tasksLen = 0;
        }

        if (directory) {
            data->directory = strdup(directory);
        } else {
            data->directory = NULL;
        }

        //data->timeoutfunction = timeoutfunction;
        data->monotonicSecondEndTime = monotonicSecondTimeGet() + timeout;
        if (cacertPath) {
            data->cacertPath = strdup(cacertPath);
        } else {
            data->cacertPath = NULL;
        }
    }
    return data;
}
static void rrIdiagWorkerTaskDownloadDataDel(ADM_RR_IdiagWorkerTaskDownloadData_T *data) {
    if (data->backofficeaddress) {
        free(data->backofficeaddress);
    }
    if (data->tasks) {
        for (D32S i = 0; i < data->tasksLen; ++i) {
            rdsTaskDeInit(data->tasks + i);
        }
        free(data->tasks);
    }
    if (data->directory) {
        free(data->directory);
    }
    if (data->cacertPath) {
        free(data->cacertPath);
    }

    free(data);
}

typedef struct {
    DCHAR *backofficeaddress;
    ADM_RDS_Response_F response;
    RDS_uploadloginfo uploadlog;
    //ADM_RDS_Response_timeout timeoutfunction;
    D32U monotonicSecondEndTime;
} ADM_RR_IdiagWorkerUploadLogData_T;
static ADM_RR_IdiagWorkerUploadLogData_T *rrIdiagWorkerUploadLogDataNew(char const *backofficeaddress,
                                                                        ADM_RDS_Response_F response,
                                                                        RDS_uploadloginfo *uploadlog,                                                                   
                                                                        D32U timeout) {
    ADM_RR_IdiagWorkerUploadLogData_T *data
        = (ADM_RR_IdiagWorkerUploadLogData_T *)malloc(sizeof(ADM_RR_IdiagWorkerUploadLogData_T));
    if (data == NULL) {
        log_w("malloc error");
    } else {
        if (backofficeaddress) {
            data->backofficeaddress = strdup(backofficeaddress);
        } else {
            data->backofficeaddress = NULL;
        }
        data->response = response;
        rdsUploadLogInfoInit(&data->uploadlog);
        rdsUploadLogInfoClone(uploadlog, &data->uploadlog);

        //data->timeoutfunction = timeoutfunction;
        data->monotonicSecondEndTime = monotonicSecondTimeGet() + timeout;
    }
    return data;
}
static void rrIdiagWorkerUploadLogDataDel(ADM_RR_IdiagWorkerUploadLogData_T *data) {
    if (data->backofficeaddress) {
        free(data->backofficeaddress);
    }
    rdsUploadLogInfoDeInit(&data->uploadlog);
    free(data);
}

static void rrIdiagWorkerRegister(ADM_RR_IdiagWorkerVinRegisterData_T *data) {
    D32S result = ADM_E_UNKNOWN;

    DCHAR *vin = data->vin;
    D64S timestamp = data->timestamp;
    DCHAR *backofficeaddress = data->backofficeaddress;

    log_d("vin:%s timestamp:%lld backofficeaddress:%s",
          vin ? vin : "null",
          timestamp,
          backofficeaddress ? backofficeaddress : "null");
    if (vin == NULL || backofficeaddress == NULL) {
        result = ADM_E_INVAL_PARAM;
    } else {
        result = adm_rdc_register(vin, timestamp, backofficeaddress);
        if (result == ADM_E_OK) {
        } else {
            log_w("adm_rdc_register result:%d", result);
        }
    }

    D8U ret = kRRDiagEcodeFailed;
    if (result == ADM_E_OK) {
        ret = kRRDiagEcodeSuccess;
    } else if (result == ADM_E_OPERATION_TIMEDOUT) {
        ret = kRRDiagEcodeTimeout;
    }


    ADM_RDS_ResponseInfo_T responseInfo = {
        .status = ADM_RDS_ResponseInfo_T::ADM_RDS_ResponseStatus_Register,
        .result = ret,
    };


    if (data->response) {
        data->response(&responseInfo);
    }
}

static DBOOL checkFreeSpace(ADM_RDS_TaskInfo_T *rds, DCHAR *directory) {
    D64S needSpace = 0;
    for (D32S i = 0; i < rds->Scriptnum; ++i) {
        needSpace += rds->scriptinfo[i].scriptSize;

    }

    struct statfs diskInfo;
    statfs(directory, &diskInfo);
    D64S freeSpace = diskInfo.f_bavail * diskInfo.f_bsize;
    log_i("freeSpace:%lld needSpace:%lld", freeSpace, needSpace);

    DBOOL dRet = 0;
    if ((freeSpace / 10 * 9) < needSpace) {
    } else {
        dRet = 1;
    }
    return dRet;
}

static void rdsClearRdsTaskInfoScriptPath(ADM_RDS_TaskInfo_T *rds) {
    for (D32S i = 0; i < rds->Scriptnum; ++i) {
        if (rds->scriptinfo[i].scriptPath) {
            adm_free(rds->scriptinfo[i].scriptPath);
            rds->scriptinfo[i].scriptPath = NULL;
        }
        rds->scriptinfo[i].scriptpathlength = 0;
    }
}

#define URL_FORMAT_MAX_LENGTH 10
static void readFileFormatFromUrl(DCHAR *url, DCHAR *format, D32S formatLen) {
    D32S index = strlen(url);
    DCHAR *dst = NULL;
    for (int i = 0; i < URL_FORMAT_MAX_LENGTH; ++i) {
        if (index > 0) {
        } else {
            break;
        }
        if (url[index] == '.') {
            dst = url + index;
        }
        --index;
    }

    if (dst) {
        strncpy(format, dst, formatLen);
    } else {
        strncpy(format, ".zip", formatLen);
    }
}

static size_t httpFileWriteCallback(DCHAR *buffer, size_t size, size_t nitems, void *userdata) {
    size_t wrote_size = fwrite(buffer, size, nitems, (FILE *)userdata);
    long wrote_bytes = (wrote_size == nitems) ? (size * nitems) : 0;
    return wrote_bytes;
}

static D32S httpDownload(
    DCHAR *url, DCHAR *hash, D64S size, DCHAR *file, DBOOL resume, DCHAR *cacertPath, D32U monotonicSecondEndTime) {
    FILE *fp = fopen(file, (resume ? "ab" : "wb"));
    if (fp == NULL) {
        log_e("open file %s error %s", file, strerror(errno));
        return ADM_E_OPEN_FILE_FAIL;
    }

    D32S ret = ADM_E_UNKNOWN;
    D64S rangFrom = ftell(fp);
    if (rangFrom == -1) {
        log_e("get file %s size error %s", file, strerror(errno));
        ret = ADM_E_READ_FILE_FAIL;
    } else if (rangFrom > size) {
        log_e("rangFrom is %lld, but size is %lld", rangFrom, size);
        ret = ADM_E_VERIFY_SIZE_FAIL;
    } else if (rangFrom == size) {
        log_w("rangFrom is %lld, but size is %lld", rangFrom, size);
        ret = 0;
    } else {
        D32U timeout = timeoutCalculate(monotonicSecondEndTime);
        if (timeout == 0) {
            ret = ADM_E_OPERATION_TIMEDOUT;
        } else {
            DCHAR rang[128];
            snprintf(rang, 128, "%lld-", rangFrom);

            ADM_Http_T http = ADM_Http_Initializer;
            http.url = url;
            http.cacert = cacertPath;
            http.timeout = timeout;
            http.writeFunc = httpFileWriteCallback;
            http.writePriv = fp;
            http.method = ADM_Http_T::METHOD_GET;
            http.u.get.rang = rang;
            http.u.get.cancelFunc = NULL;
            http.u.get.cancelPriv = NULL;
            ret = adm_httpPerform(&http, NULL);
            if (ret) {
                log_e("adm_httpPerform error %d", ret);
            }
        }
    }
    fclose(fp);

    if (ret) {
    } else {
        DCHAR h[128];
        if (adm_md5File(file, h, sizeof(h))) {
            if (adm_strcmp(hash, h) == 0) {
            } else {
                log_e("verify hash failed, expect:[%s] but[%s]", hash, h);
                ret = ADM_E_VERIFY_SHA256_FAIL;
            }
        } else {
            log_e("adm_md5File error");
            ret = ADM_E_NO_MEMORY;
        }
    }

    return ret;
}

static D32S rdsDownloadSimple(DCHAR *url,
                              DCHAR *hash,
                              D64S size,
                              DCHAR *file,
                              D32S retryDownloadTimes,
                              DCHAR *cacertPath,
                              D32U monotonicSecondEndTime) {
    D32S downloadTimes = 1;
    if (retryDownloadTimes > 0) {
        downloadTimes += retryDownloadTimes;
    } else {
        log_w("retryDownloadTimes:%d", retryDownloadTimes);
    }

    D32S ret = ADM_E_UNKNOWN;
    DBOOL resume = 1;
    for (D32S i = 0; i < downloadTimes; ++i) {
        ret = httpDownload(url, hash, size, file, resume, cacertPath, monotonicSecondEndTime);
        log_i("httpDownload ret:%d", ret);
        if (ret == ADM_E_OK || ret == ADM_E_OPERATION_TIMEDOUT) {
            break;
        } else if (ret == ADM_E_VERIFY_SHA256_FAIL) {
            resume = 0;
        } else {
            resume = 1;
            if ((i + 1) < downloadTimes) {
                // sleep((i +1) * 10);
                for (D32S j = 0; j < ((i + 1) * 10); ++j) {
                    sleep(1);
                    if (timeoutCalculate(monotonicSecondEndTime) == 0) {
                        ret = ADM_E_OPERATION_TIMEDOUT;
                        break;
                    }
                }
            }

            if (ret == ADM_E_OPERATION_TIMEDOUT) {
                break;
            }
        }
    }
    return ret;
}

static D32S rdsDownload(ADM_RDS_TaskInfo_T *rds,
                        DCHAR *directory,
                        DCHAR *backofficeaddress,
                        DCHAR *cacertPath,
                        D32U monotonicSecondEndTime) {
    if (rds->scriptinfo && (rds->Scriptnum > 0)) {
    } else {
        log_w("Scriptnum:%d", rds->Scriptnum);
        return ADM_E_OK;
    }

    if (rds->action == ADM_RDS_TaskInfo_T::ACTION_TASK_DEL) {
        rdsClearRdsTaskInfoScriptPath(rds);
        return ADM_E_OK;
    }

    D32S ret = ADM_E_UNKNOWN;
    ADM_RDC_ReportDownloadStatus_E downloadStatus;
    ADM_RDC_ReportDownloadFailReason_E downloadFailReason;

    downloadStatus = ADM_RDC_ReportDownloadStatus_Start;
    downloadFailReason = ADM_RDC_ReportDownloadFailReason_Ok;
    ret = adm_rdc_reportDownload(
        rds->sessionId, rds->taskId, rds->taskVersion, downloadStatus, downloadFailReason, backofficeaddress);
    if (ret) {
        log_w("adm_rdc_reportDownload error:%d", ret);
    }

    if (checkFreeSpace(rds, directory)) {
        D32S retryDownloadTimes = 3 /*TODO from config*/;

        DCHAR url[1024];
        DCHAR file[1024];
        DCHAR format[16];
        for (D32S i = 0; i < rds->Scriptnum; ++i) {
            if (rds->scriptinfo[i].scriptPath == NULL) {
                log_e("taskId:%lld scriptId:%d lack script url", rds->taskId, rds->scriptinfo[i].scriptId);
                ret = ADM_E_INVAL_PARAM;
                break;
            }

            snprintf(url, sizeof(url) / sizeof(DCHAR), "%s", rds->scriptinfo[i].scriptPath);
            adm_free(rds->scriptinfo[i].scriptPath);
            rds->scriptinfo[i].scriptPath = NULL;
            rds->scriptinfo[i].scriptpathlength = 0;

            readFileFormatFromUrl(url, format, sizeof(format) / sizeof(DCHAR));
            snprintf(file,
                     sizeof(file) / sizeof(DCHAR),
                     "%stask.%lu.address.0X%X.script.%u.index.0X%X%s",
                     directory,
                     rds->taskId,
                     rds->scriptinfo[i].diagnosticaddress,
                     rds->scriptinfo[i].scriptId,
                     i,
                     format);

            if (rds->scriptinfo[i].scriptHash == NULL) {
                log_e("taskId:%lld scriptId:%d lack script hash", rds->taskId, rds->scriptinfo[i].scriptId);
                ret = ADM_E_INVAL_PARAM;
                break;
            }

            ret = rdsDownloadSimple(url,
                                    rds->scriptinfo[i].scriptHash,
                                    rds->scriptinfo[i].scriptSize,
                                    file,
                                    retryDownloadTimes,
                                    cacertPath,
                                    monotonicSecondEndTime);
            rds->scriptinfo[i].scriptPath = strdup(file);
            if (rds->scriptinfo[i].scriptPath) {
                rds->scriptinfo[i].scriptpathlength = strlen(rds->scriptinfo[i].scriptPath);
            }
            if (ret) {
                log_e("taskId:%lld rdsDownloadSimple error:%d", rds->taskId, ret);
                break;
            }
        }
    } else {
        log_e("checkFreeSpace error");
        ret = ADM_E_SPACE_NOT_ENOUGH;
    }

    if (ret) {
        downloadStatus = ADM_RDC_ReportDownloadStatus_Failed;
    } else {
        downloadStatus = ADM_RDC_ReportDownloadStatus_Success;
    }

    switch (ret) {
        case ADM_E_OK:
            downloadFailReason = ADM_RDC_ReportDownloadFailReason_Ok;
            break;
        case ADM_E_VERIFY_SHA256_FAIL:
            downloadFailReason = ADM_RDC_ReportDownloadFailReason_VerifyHashFailed;
            break;
        case ADM_E_SPACE_NOT_ENOUGH:
            downloadFailReason = ADM_RDC_ReportDownloadFailReason_NotEnoughSpace;
            break;
        case ADM_E_COULDNT_CONNECT:
            downloadFailReason = ADM_RDC_ReportDownloadFailReason_NoNetWorkConnection;
            break;
        case ADM_E_OPERATION_TIMEDOUT:
            downloadFailReason = ADM_RDC_ReportDownloadFailReason_DownloadFileTimeout;
            break;
        case ADM_E_URL_MALFORMAT:
        case ADM_E_COULDNT_RESOLVE_HOST:
        case ADM_E_HTTP_RETURNED_ERROR:
        case ADM_E_UPLOAD_FAILED:
        case ADM_E_RANGE_ERROR:
        case ADM_E_BAD_DOWNLOAD_RESUME:
        case ADM_E_TOO_MANY_REDIRECTS:
        case ADM_E_GOT_NOTHING:
        case ADM_E_RECV_ERROR:
        case ADM_E_FILESIZE_EXCEEDED:
        case ADM_E_LOGIN_DENIED:
        case ADM_E_REMOTE_FILE_NOT_FOUND:
        case ADM_E_SSL_CONNECT_ERROR:
        case ADM_E_PEER_FAILED_VERIFICATION:
        case ADM_E_SSL_ENGINE_NOTFOUND:
        case ADM_E_SSL_ENGINE_SETFAILED:
        case ADM_E_SSL_CERTPROBLEM:
        case ADM_E_SSL_CIPHER:
        case ADM_E_SSL_CACERT:
        case ADM_E_SSL_ENGINE_INITFAILED:
        case ADM_E_SSL_CACERT_BADFILE:
            downloadFailReason = ADM_RDC_ReportDownloadFailReason_NetworkAccessException;
            break;
        default:
            downloadFailReason = ADM_RDC_ReportDownloadFailReason_OtherError;
            break;
    }

    adm_rdc_reportDownload(
        rds->sessionId, rds->taskId, rds->taskVersion, downloadStatus, downloadFailReason, backofficeaddress);
    return ret;
}

typedef struct {
    ADM_RDS_TaskInfo_T *rds;
    DCHAR *directory;
    DCHAR *backofficeaddress;
    D32S result;
    D32U monotonicSecondEndTime;
    DCHAR *cacertPath;
} RdcShowTaskInfoParam_T;
static void rdcShowTaskInfo(ADM_RDC_TaskInfo_T *taskInfo, void *priv) {
    RdcShowTaskInfoParam_T *p = (RdcShowTaskInfoParam_T *)priv;
    ADM_RDS_TaskInfo_T *rds = p->rds;
    DCHAR *directory = p->directory;
    DCHAR *backofficeaddress = p->backofficeaddress;
    DCHAR *cacertPath = p->cacertPath;
    D32U monotonicSecondEndTime = p->monotonicSecondEndTime;
    rdsTaskInfoInit(rds, taskInfo);
    D32S result = rdsDownload(rds, directory, backofficeaddress, cacertPath, monotonicSecondEndTime);
    if (result == ADM_E_OK) {
        rdsTaskInfoShow(rds);
    } else {
        log_w("rdsDownload error:%d", result);
    }
    p->result = result;
}

typedef struct {
    ADM_RDS_TaskInfo_T *rds;
    D32S rdsLen;
    DCHAR *directory;
    DCHAR *backofficeaddress;
    D32S result;
    D32U monotonicSecondEndTime;
    DCHAR *cacertPath;
} RdcTaskShowParam_T;
static void rdcTaskShow(ADM_RDC_Task_T tasks[], D32S tasksLen, void *priv) {
    D32S result = ADM_E_UNKNOWN;
    ADM_RDS_TaskInfo_T *rds = NULL;
    D32S rdsLen = 0;
    RdcTaskShowParam_T *param = (RdcTaskShowParam_T *)priv;
    DCHAR *directory = param->directory;
    DCHAR *backofficeaddress = param->backofficeaddress;
    DCHAR *cacertPath = param->cacertPath;
    D32U monotonicSecondEndTime = param->monotonicSecondEndTime;

    rds = (ADM_RDS_TaskInfo_T *)adm_malloc(tasksLen * sizeof(ADM_RDS_TaskInfo_T));
    if (rds == NULL) {
        log_w("malloc error");
        result = ADM_E_NO_MEMORY;
    } else {
        adm_memset(rds, 0x00, tasksLen * sizeof(ADM_RDS_TaskInfo_T));
        rdsLen = tasksLen;

        RdcShowTaskInfoParam_T p;
        p.directory = directory;
        p.backofficeaddress = backofficeaddress;
        p.monotonicSecondEndTime = monotonicSecondEndTime;
        p.cacertPath = cacertPath;
        for (D32S i = 0; i < tasksLen; ++i) {
            p.rds = rds + i;
            p.result = ADM_E_UNKNOWN;
            result = adm_rdc_taskInfoGet(tasks + i, rdcShowTaskInfo, &p, backofficeaddress);
            if (result == ADM_E_OK) {
                result = p.result;
            } else {
                log_w("adm_rdc_taskInfoGet error:%d", result);
            }
            if (result == ADM_E_OK) {
            } else {
                break;
            }
        }
    }

    param->result = result;
    if (result == ADM_E_OK) {
        param->rds = rds;
        param->rdsLen = rdsLen;
    } else {
        if (rds) {
            for (D32S i = 0; i < rdsLen; ++i) {
                if (rds->scriptinfo) {
                    DCHAR *scriptPath;
                    for (D32S j = 0; j < rds[i].Scriptnum; ++j) {
                        scriptPath = rds[i].scriptinfo[j].scriptPath;
                        if (scriptPath) {
                            if (strlen(scriptPath) > strlen(directory)) {
                                if (strncmp(scriptPath, directory, strlen(directory)) == 0) {
                                    log_d("remove file:%s", scriptPath);
                                    if (remove(scriptPath) == -1) {
                                        log_w("remove file:%s error %s", scriptPath, strerror(errno));
                                    }
                                }
                            }
                        }
                    }
                }
                rdsTaskInfoDeInit(rds + i);
            }
            adm_free(rds);
        }
    }
}
static void rrIdiagWorkerTaskDownload(ADM_RR_IdiagWorkerTaskDownloadData_T *data) {
    D32S result = ADM_E_UNKNOWN;
    ADM_RDS_TaskInfo_T *rds = NULL;
    D8U rdsLen = 0;

    ADM_RDS_Task_T *tasks = data->tasks;
    D32S tasksLen = data->tasksLen;
    DCHAR *directory = data->directory;
    DCHAR *backofficeaddress = data->backofficeaddress;
    DCHAR *cacertPath = data->cacertPath;
    D32U monotonicSecondEndTime = data->monotonicSecondEndTime;

    log_d("tasksLen:%d directory:%s backofficeaddress:%s cacertPath:%s",
          tasksLen,
          directory ? directory : "null",
          backofficeaddress ? backofficeaddress : "null",
          cacertPath ? cacertPath : "null");
    if (directory == NULL || backofficeaddress == NULL || cacertPath == NULL) {
        result = ADM_E_INVAL_PARAM;
    } else {
        if (adm_createDir(directory)) {
            log_w("adm_createDir %s failed", directory);
            result = ADM_E_OPEN_FILE_FAIL;
        } else {
            DCHAR cmd[1024];
            snprintf(cmd, sizeof(cmd), "rm %s* -fr", directory);
            log_i("cmd:[%s]", cmd);
            system(cmd);

            RdcTaskShowParam_T param = {.rds = NULL,
                                        .rdsLen = 0,
                                        .directory = directory,
                                        .backofficeaddress = backofficeaddress,
                                        .result = ADM_E_UNKNOWN,
                                        .monotonicSecondEndTime = monotonicSecondEndTime,
                                        .cacertPath = cacertPath};
            if (tasksLen > 0) {
                if (tasks == NULL) {
                    log_w("nulll tasks");
                    result = ADM_E_INVAL_PARAM;
                } else {
                    ADM_RDC_TaskTitle_T *tts;
                    D32S ttsLen = rdcTaskTitleListNew(tasks, tasksLen, &tts);
                    if (ttsLen == 0) {
                        log_w("rdcTaskTitleListNew error");
                        result = ADM_E_INVAL_PARAM;
                    } else {
                        result = adm_rdc_taskCheck(tts, ttsLen, rdcTaskShow, &param, backofficeaddress);
                        if (result == ADM_E_OK) {
                            rds = param.rds;
                            rdsLen = param.rdsLen;
                            result = param.result;
                        } else {
                            log_w("adm_rdc_taskCheck error:%d", result);
                        }
                        rdcTaskTitleListDel(tts, ttsLen);
                    }
                }
            } else {
                result = adm_rdc_taskCheck(NULL, 0, rdcTaskShow, &param, backofficeaddress);
                if (result == ADM_E_OK) {
                    rds = param.rds;
                    rdsLen = param.rdsLen;
                    result = param.result;
                } else {
                    log_w("adm_rdc_taskCheck error:%d", result);
                }
            }
        }
    }

    D8U ret = kRRDiagEcodeFailed;
    if (result == ADM_E_OK) {
        ret = kRRDiagEcodeSuccess;
    } else if (result == ADM_E_OPERATION_TIMEDOUT) {
        ret = kRRDiagEcodeTimeout;
    }

    ADM_RDS_ResponseInfo_T responseInfo = {
        .status = ADM_RDS_ResponseInfo_T::ADM_RDS_ResponseStatus_Download,
        .u = {
            .taskInfos = {
                .taskInfos = rds,
                .taskInfosLen = rdsLen
            },
        },
        .result = ret
    };


    if (data->response) {
        data->response(&responseInfo);
    }

    if (rds) {
        for (D32S i = 0; i < rdsLen; ++i) {
            rdsTaskInfoDeInit(rds + i);
        }
        adm_free(rds);
    }
}

static void threeByteRandGet(char *myRand) {
    int a = rand() % 10;
    int b = rand() % 10;
    int c = rand() % 10;
    sprintf(myRand, "%d%d%d", a, b, c);
}
static void nowTimeGet(char *nowTime) {
    char acYear[5] = {0};
    char acMonth[5] = {0};
    char acDay[5] = {0};
    char acHour[5] = {0};
    char acMin[5] = {0};
    char acSec[5] = {0};
    char myRand[5] = {0};
    time_t now;
    struct tm *timenow;
    time(&now);
    timenow = localtime(&now);
    strftime(acYear, sizeof(acYear), "%Y", timenow);
    strftime(acMonth, sizeof(acMonth), "%m", timenow);
    strftime(acDay, sizeof(acDay), "%d", timenow);
    strftime(acHour, sizeof(acHour), "%H", timenow);
    strftime(acMin, sizeof(acMin), "%M", timenow);
    strftime(acSec, sizeof(acSec), "%S", timenow);
    threeByteRandGet(myRand);
    strncat(nowTime, acYear, 4);
    strncat(nowTime, acMonth, 2);
    strncat(nowTime, acDay, 2);
    strncat(nowTime, acHour, 2);
    strncat(nowTime, acMin, 2);
    strncat(nowTime, acSec, 2);
    strncat(nowTime, myRand, 3);
}

static void rrIdiagWorkerReportLog(ADM_RR_IdiagWorkerUploadLogData_T *data) {
    D32S result = ADM_E_UNKNOWN;
    RDS_uploadloginfo *upload = &data->uploadlog;

    DCHAR *backofficeaddress = data->backofficeaddress;
    DCHAR *sessionId = upload->sessionId;
    D32S sessionIdlength = upload->sessionIdlength;
    D64S executeStartTime = (D64S)upload->executeStartTime;
    D64S taskId = upload->taskId;
    D64S taskVersion = upload->taskVersion;
    D64S executeEndTime = (D64S)upload->executeEndTime;
    ADM_RDS_ReportLogFileType_E fileType = upload->fileType;
    DCHAR *uploadFile = upload->uploadFile;
    D32S count = upload->count;
    D64S timestamp = (D64S)upload->timestamp;
    DCHAR *uploaddirectory = upload->uploaddirectory;
    D32U monotonicSecondEndTime = data->monotonicSecondEndTime;

    log_d(
        "backofficeaddress:%s sessionId:%s sessionIdlength:%d executeStartTime:%lld taskId:%lld taskVersion:%lld "
        "executeEndTime:%lld fileType:%d uploadFile:%s count:%d timestamp:%lld uploaddirectory:%s "
        "monotonicSecondEndTime:%u",
        backofficeaddress ? backofficeaddress : "null",
        sessionId ? sessionId : "null",
        sessionIdlength,
        executeStartTime,
        taskId,
        taskVersion,
        executeEndTime,
        fileType,
        uploadFile ? uploadFile : "null",
        count,
        timestamp,
        uploaddirectory ? uploaddirectory : "null",
        monotonicSecondEndTime);

    if (backofficeaddress == NULL || sessionId == NULL || uploadFile == NULL || uploaddirectory == NULL) {
        result = ADM_E_INVAL_PARAM;
    } else {
        D32U timeout = timeoutCalculate(monotonicSecondEndTime);
        if (timeout == 0) {
            result = ADM_E_OPERATION_TIMEDOUT;
        } else {
            ADM_RDC_ReportLogFileType_E type = ADM_RDC_ReportLogFileType_Execute;
            switch (fileType) {
                case ADM_RDS_ReportLogFileType_Diagnostic:
                    type = ADM_RDC_ReportLogFileType_Diagnostic;
                    break;
                case ADM_RDS_ReportLogFileType_Application:
                    type = ADM_RDC_ReportLogFileType_Application;
                    break;
                case ADM_RDS_ReportLogFileType_Execute:
                    type = ADM_RDC_ReportLogFileType_Execute;
                    break;
            }
            DCHAR file[256];
            snprintf(file, sizeof(file) / sizeof(DCHAR), "%s%s", uploaddirectory, uploadFile);
            log_d("uploadFile:%s", file);

            DCHAR nowTime[128] = {0};
            nowTimeGet(nowTime);
            DCHAR path[256];
            snprintf(path, sizeof(path) / sizeof(DCHAR), "%s%s.log", uploaddirectory, nowTime);

            if (access(file, F_OK) == -1) {
                log_w("file:%s not exsit %s", file, strerror(errno));
                result = ADM_E_FILE_NOT_EXIST;
            } else {
                DCHAR cmd[1024];
                snprintf(cmd, sizeof(cmd) / sizeof(DCHAR), "cp %s %s", file, path);
                log_d("cmd[%s]", cmd);
                system(cmd);
                if (access(path, F_OK) == -1) {
                    log_w("file:%s not exsit %s", path, strerror(errno));
                    result = ADM_E_FILE_NOT_EXIST;
                } else {
                    result = adm_rdc_reportLog(executeStartTime,
                                               sessionId,
                                               taskId,
                                               taskVersion,
                                               executeEndTime,
                                               type,
                                               path,
                                               count,
                                               timestamp,
                                               backofficeaddress,
                                               timeout);
                    if (result == ADM_E_OK) {
                    } else {
                        log_w("adm_rdc_reportLog error:%d", result);
                    }
                    remove(path);
                }
            }
        }
    }

    D8U ret = kRRDiagEcodeFailed;
    if (result == ADM_E_OK) {
        ret = kRRDiagEcodeSuccess;
    } else if (result == ADM_E_OPERATION_TIMEDOUT) {
        ret = kRRDiagEcodeTimeout;
    }

    ADM_RDS_ResponseInfo_T responseInfo = {
        .status = ADM_RDS_ResponseInfo_T::ADM_RDS_ResponseStatus_ReportLog,
        .result = ret,
        
    };

    responseInfo.u.rdsUploadLogInfo = &data->uploadlog;
    
    if (data->response) {
        data->response(&responseInfo);
    }
}

static void rrIdiagWorkerEngineVinRegister(void *param) {
    ADM_RR_IdiagWorkerVinRegisterData_T *data = (ADM_RR_IdiagWorkerVinRegisterData_T *)param;
    rrIdiagWorkerRegister(data);
    rrIdiagWorkerVinRegisterDataDel(data);
}

static void rrIdiagWorkerEngineTaskDownload(void *param) {
    ADM_RR_IdiagWorkerTaskDownloadData_T *data = (ADM_RR_IdiagWorkerTaskDownloadData_T *)param;
    rrIdiagWorkerTaskDownload(data);
    rrIdiagWorkerTaskDownloadDataDel(data);
}

static void rrIdiagWorkerEngineUploadLog(void *param) {
    ADM_RR_IdiagWorkerUploadLogData_T *data = (ADM_RR_IdiagWorkerUploadLogData_T *)param;
    rrIdiagWorkerReportLog(data);
    rrIdiagWorkerUploadLogDataDel(data);
}

typedef struct {
    pthread_mutex_t mutex;
    ADM_RDS_Response_F response;
    //ADM_RDS_Response_timeout timeoutfunction;
    unsigned short Time1;
    unsigned short Time2;
    char *cacertPath;
    ADM_LIB_Workqueue_T *workerVinRegister;
    ADM_LIB_Workqueue_T *workerTaskDownload;
    ADM_LIB_Workqueue_T *workerUploadLog;
   

} ADM_RR_Idiag_T;



static void rrIdiagInit(ADM_RR_Idiag_T *diag,
                        ADM_RDS_Response_F response,
                        unsigned short Time1,
                        unsigned short Time2,
                        char *cacertPath) {

    pthread_mutex_init(&diag->mutex, NULL);
    diag->response = response;
    //diag->timeoutfunction = timeoutfunction;
    diag->Time1 = Time1;
    diag->Time2 = Time2;
    if (cacertPath) {
        diag->cacertPath = strdup(cacertPath);
    } else {
        diag->cacertPath = NULL;
    }

    diag->workerVinRegister = adm_WorkqueueNew(1, rrIdiagWorkerEngineVinRegister);
    diag->workerTaskDownload = adm_WorkqueueNew(1, rrIdiagWorkerEngineTaskDownload);
    diag->workerUploadLog = adm_WorkqueueNew(1, rrIdiagWorkerEngineUploadLog);

}
static void rrIdiagDeInit(ADM_RR_Idiag_T *diag) {


    adm_WorkqueueDel(diag->workerVinRegister);
    adm_WorkqueueDel(diag->workerTaskDownload);
    adm_WorkqueueDel(diag->workerUploadLog);
    
    if (diag->cacertPath) {
        free(diag->cacertPath);
    }
    

    pthread_mutex_destroy(&diag->mutex);


}


static void rrIdiagVinRegister(ADM_RR_Idiag_T *diag, char *vin, D64S timestamp, char *backofficeaddress) {
    pthread_mutex_lock(&diag->mutex);
    ADM_RR_IdiagWorkerVinRegisterData_T *data
        = rrIdiagWorkerVinRegisterDataNew(backofficeaddress, diag->response, vin, timestamp);
    if (data == NULL) {
        log_w("rrIdiagWorkerVinRegisterDataNew error");
    } else {
        if (adm_WorkqueueAdd(diag->workerVinRegister, data)) {
            log_w("adm_WorkqueueAdd error");
            rrIdiagWorkerVinRegisterDataDel(data);
        }
    }
    pthread_mutex_unlock(&diag->mutex);
}

static void rrIdiagTaskDownload(
    ADM_RR_Idiag_T *diag, ADM_RDS_Task_T tasks[], int tasksLen, char *directory, char *backofficeaddress) {
    pthread_mutex_lock(&diag->mutex);
    ADM_RR_IdiagWorkerTaskDownloadData_T *data = rrIdiagWorkerTaskDownloadDataNew(backofficeaddress,
                                                                                  diag->response,
                                                                                  tasks,
                                                                                  tasksLen,
                                                                                  directory,
                                                                                  diag->Time1,
                                                                                  diag->cacertPath);
    if (data == NULL) {
        log_w("rrIdiagWorkerTaskDownloadDataNew error");
    } else {
        if (adm_WorkqueueAdd(diag->workerTaskDownload, data)) {
            log_w("adm_WorkqueueAdd error");
            rrIdiagWorkerTaskDownloadDataDel(data);
        }
    }
    pthread_mutex_unlock(&diag->mutex);
}

static void rrIdiagReportLog(ADM_RR_Idiag_T *diag, RDS_uploadloginfo *uploadlog, char const *backofficeaddress) {
    pthread_mutex_lock(&diag->mutex);
    ADM_RR_IdiagWorkerUploadLogData_T *data = rrIdiagWorkerUploadLogDataNew(
        backofficeaddress, diag->response, uploadlog, diag->Time2);
    if (data == NULL) {
        log_w("rrIdiagWorkerUploadLogDataNew error");
    } else {
        if (adm_WorkqueueAdd(diag->workerUploadLog, data)) {
            rrIdiagWorkerUploadLogDataDel(data);
            log_w("adm_WorkqueueAdd error");
        }
    }
    pthread_mutex_unlock(&diag->mutex);
}

static ADM_RR_Idiag_T s_diag;






ADM_EXPORT_API void adm_rds_init(ADM_RDS_Response_F response,
                                 unsigned short Time1,
                                 unsigned short Time2,
                                 char *logdirectory,
                                 char *certificatedirectory) {
    if (kInitOk > 0) {
      
        printf("adm_rds_init  had already finished, return right now \n");   
        return;
    }

    if (logdirectory) {
        char logPath[256] = { 0 };
        snprintf(logPath, sizeof(logPath) / sizeof(char), "%s%s", logdirectory, ADM_CONFIG_DC_LOG_FILE_NAME);
        adm_initLog(logPath, NULL);
    } else {
        adm_initLog(NULL, NULL);
    }


    adm_sdkVersionInit(ADM_CONFIG_SDK_VERSION);
    
    DCHAR *sdkVersion = (DCHAR *)adm_sdkVersionGet();
    
    log_i("sdkVersion:%s", sdkVersion);

    adm_httpGlobalInit();

    DCHAR cacertPath[256];
    snprintf(cacertPath,
             sizeof(cacertPath) / sizeof(DCHAR),
             "%s%s",
             certificatedirectory ? certificatedirectory : "/etc/ssl/certs/",
             ADM_CONFIG_SERVER_CERT_FILE);


    ADM_RDC_Param_T rdcParam = {.signatureKey = (char *)ADM_CONFIG_HTTP_SIGNATURE_KEY,
                                .cacertPath = cacertPath,
                                .cryptoKey = (char *)ADM_CONFIG_HTTP_CRYPTO_KEY,
                                .sdkVersion = sdkVersion};
                                
    D32S result = adm_rdc_init(&rdcParam);
    if (result == ADM_E_OK) {
    } else {
        log_w("adm_rdc_init error:%d", result);
    }

    rrIdiagInit(&s_diag, response, Time1, Time2, cacertPath);

    adm_rdc_start();

    kInitOk = 1;

}

ADM_EXPORT_API void adm_rds_deinit() {

    if (kInitOk > 0) {

        log_d("adm_rds_deinit");
        rrIdiagDeInit(&s_diag);
        adm_rdc_deinit();
        adm_httpGlobalDeInit();
        adm_deinitLog();
    } 

    kInitOk = 0;
}

ADM_EXPORT_API void adm_rds_vinregister(char *vin, unsigned long timestamp, char *backofficeaddress) {
    log_d("adm_rds_vinregister start");


#ifdef ADM_CROSS_COMPILE
        // update client certificate    
        // if (!dmcDiagUpdateCertificate(s_diag.cacertPath,vin)) {
        //     log_e("dmcDiagUpdateCertificate return failed!!!");
        //     return ;
        // }
#endif


    rrIdiagVinRegister(&s_diag, vin, (D64S)timestamp, backofficeaddress);
    log_d("adm_rds_vinregister end");
}

ADM_EXPORT_API void adm_rds_taskDownload(ADM_RDS_Task_T tasks[],
                                         int tasksLen,
                                         char *directory,
                                         char *backofficeaddress) {
    log_d("adm_rds_taskDownload start");
    rrIdiagTaskDownload(&s_diag, tasks, tasksLen, directory, backofficeaddress);
    log_d("adm_rds_taskDownload end");
}

ADM_EXPORT_API void adm_rds_reportLog(RDS_uploadloginfo *uploadlog, char const *backofficeaddresss) {
    log_d("adm_rds_reportLog start");
    rrIdiagReportLog(&s_diag, uploadlog, backofficeaddresss);
    log_d("adm_rds_reportLog end");
}
