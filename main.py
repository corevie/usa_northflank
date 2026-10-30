#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Cloudflare IP 优选工具 (合并版)
流程: 多源下载合并 → TCP筛选 → 可用性检测 → 带宽测速 → 输出 → 推送GitHub
依赖: requests, curl (系统自带)
配置: config.json
"""

import requests
import socket
import time
import sys
import re
import os
import gc
import ssl
import json
import subprocess
import shutil
import urllib.request
import urllib.parse
from collections import defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed, wait, FIRST_COMPLETED
from functools import lru_cache
from typing import Optional, List, Set

# ==================== 预编译正则 ====================
NODE_PATTERN = re.compile(r"^(\d+\.\d+\.\d+\.\d+):(\d+)#(.+)$")
IP_PORT_PATTERN = re.compile(r"^(\d+\.\d+\.\d+\.\d+):(\d+)#")
IPV4_RE = re.compile(r'^((25[0-5]|2[0-4]\d|1\d{2}|[1-9]?\d)\.){3}(25[0-5]|2[0-4]\d|1\d{2}|[1-9]?\d)$')
LINE_RE = re.compile(r'^([\d.]+):(\d+)(?:#[\w\-]+)?(?:\s*[|#].*)?$')
REGION_RE = re.compile(r'#([a-zA-Z]{2,3})(?:[\s|\|]|$)')
REGIONS = ["sg", "jp", "kr", "tw", "hk", "us", "de", "nl", "uk", "fr", "cn"]

# SSL 上下文 (跳过证书验证，用于 cf_merge 下载)
SSL_CONTEXT = ssl.create_default_context()
SSL_CONTEXT.check_hostname = False
SSL_CONTEXT.verify_mode = ssl.CERT_NONE

# ==================== 国家代码映射表 ====================
CN_TO_CODE = {
    "阿富汗": "AF", "奥兰群岛": "AX", "阿尔巴尼亚": "AL", "阿尔及利亚": "DZ",
    "美属萨摩亚": "AS", "安道尔": "AD", "安哥拉": "AO", "安圭拉": "AI",
    "南极洲": "AQ", "安提瓜和巴布达": "AG", "阿根廷": "AR", "亚美尼亚": "AM",
    "阿鲁巴": "AW", "澳大利亚": "AU", "奥地利": "AT", "阿塞拜疆": "AZ",
    "巴哈马": "BS", "巴林": "BH", "孟加拉国": "BD", "孟加拉": "BD",
    "巴巴多斯": "BB", "白俄罗斯": "BY", "比利时": "BE", "伯利兹": "BZ",
    "贝宁": "BJ", "百慕大": "BM", "不丹": "BT", "玻利维亚": "BO",
    "波黑": "BA", "波斯尼亚和黑塞哥维那": "BA", "博茨瓦纳": "BW",
    "布维岛": "BV", "巴西": "BR", "英属印度洋领地": "IO",
    "文莱": "BN", "保加利亚": "BG", "布基纳法索": "BF", "布隆迪": "BI",
    "柬埔寨": "KH", "喀麦隆": "CM", "加拿大": "CA", "佛得角": "CV",
    "开曼群岛": "KY", "中非": "CF", "乍得": "TD", "智利": "CL",
    "中国": "CN", "圣诞岛": "CX", "科科斯(基林)群岛": "CC",
    "哥伦比亚": "CO", "科摩罗": "KM", "刚果(布)": "CG", "刚果（布）": "CG",
    "刚果(金)": "CD", "刚果（金）": "CD", "库克群岛": "CK",
    "哥斯达黎加": "CR", "科特迪瓦": "CI", "克罗地亚": "HR", "古巴": "CU",
    "塞浦路斯": "CY", "捷克": "CZ", "丹麦": "DK", "吉布提": "DJ",
    "多米尼克": "DM", "多米尼加": "DO", "厄瓜多尔": "EC", "埃及": "EG",
    "萨尔瓦多": "SV", "赤道几内亚": "GQ", "厄立特里亚": "ER",
    "爱沙尼亚": "EE", "埃塞俄比亚": "ET", "福克兰群岛(马尔维纳斯)": "FK",
    "法罗群岛": "FO", "斐济": "FJ", "芬兰": "FI", "法国": "FR",
    "法属圭亚那": "GF", "法属波利尼西亚": "PF", "法属南部领地": "TF",
    "加蓬": "GA", "冈比亚": "GM", "格鲁吉亚": "GE", "德国": "DE",
    "加纳": "GH", "直布罗陀": "GI", "希腊": "GR", "格陵兰": "GL",
    "格林纳达": "GD", "瓜德罗普": "GP", "关岛": "GU", "危地马拉": "GT",
    "根西岛": "GG", "几内亚": "GN", "几内亚比绍": "GW", "圭亚那": "GY",
    "海地": "HT", "赫德岛和麦克唐纳群岛": "HM", "梵蒂冈": "VA",
    "洪都拉斯": "HN", "香港": "HK", "匈牙利": "HU", "冰岛": "IS",
    "印度": "IN", "印度尼西亚": "ID", "伊朗": "IR", "伊拉克": "IQ",
    "爱尔兰": "IE", "马恩岛": "IM", "以色列": "IL", "意大利": "IT",
    "牙买加": "JM", "日本": "JP", "泽西岛": "JE", "约旦": "JO",
    "哈萨克斯坦": "KZ", "肯尼亚": "KE", "基里巴斯": "KI", "朝鲜": "KP",
    "韩国": "KR", "科威特": "KW", "吉尔吉斯斯坦": "KG", "老挝": "LA",
    "拉脱维亚": "LV", "黎巴嫩": "LB", "莱索托": "LS", "利比里亚": "LR",
    "利比亚": "LY", "列支敦士登": "LI", "立陶宛": "LT", "卢森堡": "LU",
    "澳门": "MO", "北马其顿": "MK", "马其顿": "MK", "马达加斯加": "MG",
    "马拉维": "MW", "马来西亚": "MY", "马尔代夫": "MV", "马里": "ML",
    "马耳他": "MT", "马绍尔群岛": "MH", "马提尼克": "MQ",
    "毛里塔尼亚": "MR", "毛里求斯": "MU", "马约特": "YT", "墨西哥": "MX",
    "密克罗尼西亚": "FM", "摩尔多瓦": "MD", "摩纳哥": "MC", "蒙古": "MN",
    "黑山": "ME", "蒙特塞拉特": "MS", "摩洛哥": "MA", "莫桑比克": "MZ",
    "缅甸": "MM", "纳米比亚": "NA", "瑙鲁": "NR", "尼泊尔": "NP",
    "荷兰": "NL", "新喀里多尼亚": "NC", "新西兰": "NZ", "尼加拉瓜": "NI",
    "尼日尔": "NE", "尼日利亚": "NG", "纽埃": "NU", "诺福克岛": "NF",
    "北马里亚纳群岛": "MP", "挪威": "NO", "阿曼": "OM", "巴基斯坦": "PK",
    "帕劳": "PW", "巴勒斯坦": "PS", "巴拿马": "PA", "巴布亚新几内亚": "PG",
    "巴拉圭": "PY", "秘鲁": "PE", "菲律宾": "PH", "皮特凯恩": "PN",
    "波兰": "PL", "葡萄牙": "PT", "波多黎各": "PR", "卡塔尔": "QA",
    "留尼汪": "RE", "罗马尼亚": "RO", "俄罗斯": "RU", "卢旺达": "RW",
    "圣巴泰勒米": "BL", "圣赫勒拿": "SH", "圣基茨和尼维斯": "KN",
    "圣卢西亚": "LC", "圣马丁": "MF", "圣皮埃尔和密克隆": "PM",
    "圣文森特和格林纳丁斯": "VC", "萨摩亚": "WS", "圣马力诺": "SM",
    "圣多美和普林西比": "ST", "沙特阿拉伯": "SA", "沙特": "SA",
    "塞内加尔": "SN", "塞尔维亚": "RS", "塞舌尔": "SC", "塞拉利昂": "SL",
    "新加坡": "SG", "圣马丁(荷兰)": "SX", "斯洛伐克": "SK",
    "斯洛文尼亚": "SI", "所罗门群岛": "SB", "索马里": "SO", "南非": "ZA",
    "南乔治亚和南桑威奇群岛": "GS", "南苏丹": "SS", "西班牙": "ES",
    "斯里兰卡": "LK", "苏丹": "SD", "苏里南": "SR", "斯瓦尔巴和扬马延": "SJ",
    "斯威士兰": "SZ", "瑞典": "SE", "瑞士": "CH", "叙利亚": "SY",
    "台湾": "TW", "塔吉克斯坦": "TJ", "坦桑尼亚": "TZ", "泰国": "TH",
    "东帝汶": "TL", "多哥": "TG", "托克劳": "TK", "汤加": "TO",
    "特立尼达和多巴哥": "TT", "突尼斯": "TN", "土耳其": "TR",
    "土库曼斯坦": "TM", "特克斯和凯科斯群岛": "TC", "图瓦卢": "TV",
    "乌干达": "UG", "乌克兰": "UA", "阿联酋": "AE", "英国": "GB",
    "美国": "US", "美国本土外小岛屿": "UM", "乌拉圭": "UY",
    "乌兹别克斯坦": "UZ", "瓦努阿图": "VU", "委内瑞拉": "VE",
    "越南": "VN", "英属维尔京群岛": "VG", "美属维尔京群岛": "VI",
    "瓦利斯和富图纳": "WF", "西撒哈拉": "EH", "也门": "YE",
    "赞比亚": "ZM", "津巴布韦": "ZW",
}


# ==================== 加载配置文件 ====================
CONFIG_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "config.json")

def load_config():
    """加载 config.json 配置文件"""
    try:
        with open(CONFIG_FILE, "r", encoding="utf-8") as f:
            config = json.load(f)
    except FileNotFoundError:
        print(f"❌ 错误：未找到配置文件 {CONFIG_FILE}")
        sys.exit(1)
    except json.JSONDecodeError as e:
        print(f"❌ 错误：配置文件格式不正确 - {e}")
        sys.exit(1)

    defaults = {
        "USE_GLOBAL_MODE": True, "GLOBAL_TOP_N": 15, "PER_COUNTRY_TOP_N": 1,
        "BANDWIDTH_CANDIDATES": 90, "TCP_PROBES": 3, "MIN_SUCCESS_RATE": 1.0,
        "TIMEOUT": 2.0, "SOCKET_DEFAULT_TIMEOUT": 3, "PROGRESS_PRINT_INTERVAL": 1,
        "FILTER_COUNTRIES_ENABLED": False, "ALLOWED_COUNTRIES": ["US"],
        "PRE_FILTER_BLOCKED_ENABLED": True, "PRE_FILTER_BLOCKED_COUNTRIES": ["CN"],
        "PRE_FILTER_PORT_ENABLED": True, "PRE_FILTER_PORTS": [443],
        "ENABLE_WXPUSHER": True, "WXPUSHER_APP_TOKEN": "your_app_token_here",
        "WXPUSHER_UIDS": ["your_uid_here"],
        "WXPUSHER_API_URL": "https://wxpusher.zjiecode.com/api/send/message",
        "NOTIFY_TIMEOUT": 3, "NOTIFY_CONNECT_TIMEOUT": 3,
        "CF_ENABLED": True, "CF_API_TOKEN": "your_CF_API_TOKEN",
        "CF_ZONE_ID": "your_CF_ZONE_ID", "CF_DNS_RECORD_NAME": "your_CF_DNS_RECORD_NAME",
        "CF_TTL": 60, "CF_PROXIED": False, "CF_DNS_CONNECT_TIMEOUT": 3, "CF_DNS_READ_TIMEOUT": 3,
        "DNS_RECORD_TYPE": "A", "ADDITIONAL_SOURCES": [],
        "FETCH_MAX_RETRIES": 3, "FETCH_RETRY_DELAY": 3, "FETCH_TIMEOUT": 3, "FETCH_CONNECT_TIMEOUT": 3,
        "OUTPUT_FILE": "ip.txt", "ENABLE_LOGGING": False, "LOG_FILE": "cfnb.log",
        "TEST_AVAILABILITY": True, "AVAILABILITY_CHECK_API": "https://api.090227.xyz/check",
        "AVAILABILITY_TIMEOUT": 3, "AVAILABILITY_CONNECT_TIMEOUT": 3,
        "AVAILABILITY_RETRY_MAX": 2, "AVAILABILITY_RETRY_DELAY": 3,
        "FILTER_IPV6_AVAILABILITY": True, "FILTER_BLOCKED_COUNTRIES_ENABLED": True,
        "BLOCKED_COUNTRIES": [
            "BD", "BI", "BY", "CD", "CF", "CN", "CU", "DE", "ET", "HK",
            "IR", "KP", "LY", "MO", "NG", "NL", "PK", "RU", "SD", "SO",
            "SY", "TH", "TW", "UA", "VE", "VN", "YE", "ZW"
        ],
        "DNS_IP_RISK_FILTER_ENABLED": False, "DNS_IP_RISK_MAX_LEVEL": "高风险",
        "DNS_UPDATE_TARGET_COUNT": 15, "BANDWIDTH_SIZE_MB": 0.5,
        "BANDWIDTH_TIMEOUT": 3, "BANDWIDTH_RETRY_MAX": 2, "BANDWIDTH_RETRY_DELAY": 3,
        "BANDWIDTH_URL_TEMPLATE": "https://speed.cloudflare.com/__down?bytes={bytes}",
        "BANDWIDTH_PROCESS_BUFFER": 2, "BANDWIDTH_CONNECT_TIMEOUT": 3,
        "MAX_WORKERS": 200, "AVAILABILITY_WORKERS": 32, "FALLBACK_WORKERS": 32,
        "BANDWIDTH_WORKERS": 10, "DNS_UPDATE_MAX_RETRIES": 3, "DNS_UPDATE_RETRY_DELAY": 3,
        "GITHUB_SYNC_MAX_RETRIES": 3, "GITHUB_SYNC_RETRY_DELAY": 3,
        # GitHub API 推送（OUTPUT_FILE）相关配置；空字符串表示回退到 CF_MERGE_GITHUB_* 同名项
        "GITHUB_PUSH_ENABLE": True,
        "GITHUB_PUSH_TOKEN": "",
        "GITHUB_PUSH_USERNAME": "",
        "GITHUB_PUSH_REPO": "",
        "GITHUB_PUSH_BRANCH": "",
        "GITHUB_PUSH_LOCAL_PATH": "",
        "GITHUB_PUSH_REMOTE_PATH": "",
        "GITHUB_PUSH_COMMIT_MESSAGE": "Auto-update IP list",
        "GITHUB_PUSH_TIMEOUT": 30,
        "AD_HEADER_ENABLED": False, "AD_HEADER_LINES": [],
        "AD_FOOTER_ENABLED": False, "AD_FOOTER_LINES": [],
        "AD_PERLINE_ENABLED": False, "AD_PERLINE_TEXT": "",
        "IP_TXT_SHOW_BANDWIDTH": False, "IP_TXT_SHOW_LATENCY": False,
        "CHECK_CHATGPT_ENABLED": True, "CHATGPT_CHECK_TIMEOUT": 5, "CHATGPT_CHECK_WORKERS": 10,
        # cf_merge 相关配置
        "CF_MERGE_ENABLED": True,
        "CF_MERGE_URLS": [
            "https://raw.githubusercontent.com/colloq168/sub/refs/heads/raw/ALL-2026-05-18.txt",
            "https://zip.cm.edu.kg/all.txt",
            "https://countrymerge.pages.dev/all.txt",
            "https://wtf-359.pages.dev/wtf.txt",
            "https://raw.githubusercontent.com/svip-s/cloudflare_ip/refs/heads/main/best_ips.txt",
            "https://raw.githubusercontent.com/love-ztm/cfip/refs/heads/main/ubest_ips.txt",
            "https://raw.githubusercontent.com/HandsomeMJZ/cfip/refs/heads/main/best_ips.txt",
            "https://bestcf.pages.dev/tiancheng2/sg.txt",
            "https://bestcf.pages.dev/tiancheng/kr.txt",
            "https://bestcf.pages.dev/tiancheng/tw.txt",
            "https://bestcf.pages.dev/tiancheng/jp.txt",
            "https://bestcf.pages.dev/tiancheng/sg.txt",
            "https://bestcf.pages.dev/moistr/all.txt",
            "https://bestcf.pages.dev/xinyitang3/ipv4.txt",
            "https://bestcf.pages.dev/wetest/ipv4.txt",
            "https://bestcf.pages.dev/uouin/all.txt",
            "https://bestcf.pages.dev/gslege/JP.txt",
            "https://bestcf.pages.dev/gslege/DE.txt",
            "https://bestcf.pages.dev/gslege/US.txt",
            "https://bestcf.pages.dev/gslege/SG.txt",
            "https://bestcf.pages.dev/gslege/Cfxyz.txt",
            "https://bestcf.pages.dev/gslege/NL.txt",
            "https://sub.xinyitang.dpdns.org/iplist",
            "https://bestcf.pages.dev/tiancheng/all.txt",
            "https://bestcf.pages.dev/tiancheng2/all.txt",
            "https://warp-masque-bestip.pages.dev/?ips=50&level=all&port=random",
            "https://raw.githubusercontent.com/joname1/BestCFip/refs/heads/main/ipv4.txt",
            "https://bestcf.pages.dev/nirevil/ipv4.txt",
            "https://bestcf.pages.dev/mingyu/ipv4.txt",
            "https://bestcf.pages.dev/zhixuanwang/ipv4-onlyip.txt",
            "https://bestcf.pages.dev/haogege/ipv4-onlyip.txt",
            "https://raw.githubusercontent.com/Senflare/Senflare-IP/refs/heads/main/IPlist-Pro.txt",
            "https://bestcf.pages.dev/vvhan/ipv4.txt",
            "https://090227.pages.dev/bestcf?isp=all&ips=20",
            "https://bestcf.pages.dev/nirevil/ipv6.txt",
            "https://bestcf.pages.dev/mingyu/ipv6.txt",
            "https://raw.githubusercontent.com/joname1/BestCFip/refs/heads/main/ipv6.txt",
            "https://cf.junzhen.qzz.io/best_ips.txt",
            "https://cf.junzhen.qzz.io/best_ips_bj.txt",
            "https://raw.githubusercontent.com/svip-s/cloudflare_ip/refs/heads/main/best_ips.txt",
            "https://raw.githubusercontent.com/love-ztm/cfip/refs/heads/main/best_ips.txt",
            "https://raw.githubusercontent.com/love-ztm/cfip/refs/heads/main/ubest_ips.txt",
            "https://bestcf.pages.dev/vvhan/ipv6.txt"
        ],
        "CF_MERGE_OUTPUT": "cf_ips_merged.txt",
        "CF_MERGE_TIMEOUT": 15,
        "CF_MERGE_CONCURRENT": 8,
        "CF_MERGE_DEFAULT_PORT": "443",
        "CF_MERGE_PUSH_ENABLE": True,
        "CF_MERGE_GITHUB_TOKEN": "",
        "CF_MERGE_GITHUB_USERNAME": "",
        "CF_MERGE_REPO_NAME": "sub",
        "CF_MERGE_BRANCH": "raw",
        "CF_MERGE_FILE_PATH": "cf_ips_merged.txt",
        "CF_MERGE_COMMIT_MESSAGE": "Auto-update CF IPs via merge script",
    }

    for key, value in defaults.items():
        if key not in config:
            config[key] = value

    # 敏感配置优先从环境变量读取（Northflank 等平台运行时注入，避免凭据进入代码仓库）
    for _env_key in ("CF_MERGE_GITHUB_TOKEN", "CF_MERGE_GITHUB_USERNAME"):
        _env_val = os.environ.get(_env_key, "").strip()
        if _env_val:
            config[_env_key] = _env_val
    if config.get("CF_MERGE_PUSH_ENABLE") and not config.get("CF_MERGE_GITHUB_TOKEN"):
        print("⚠️  未检测到 CF_MERGE_GITHUB_TOKEN 环境变量，GitHub 推送将失败；请在部署平台环境变量中补齐")

    # GitHub 推送配置回退：空值时复用 CF_MERGE_GITHUB_* 同名项，便于单一仓库统一推送
    if not config.get("GITHUB_PUSH_TOKEN"):
        config["GITHUB_PUSH_TOKEN"] = config.get("CF_MERGE_GITHUB_TOKEN", "")
    if not config.get("GITHUB_PUSH_USERNAME"):
        config["GITHUB_PUSH_USERNAME"] = config.get("CF_MERGE_GITHUB_USERNAME", "")
    if not config.get("GITHUB_PUSH_REPO"):
        config["GITHUB_PUSH_REPO"] = config.get("CF_MERGE_REPO_NAME", "")
    if not config.get("GITHUB_PUSH_BRANCH"):
        config["GITHUB_PUSH_BRANCH"] = config.get("CF_MERGE_BRANCH", "")
    if not config.get("GITHUB_PUSH_LOCAL_PATH"):
        config["GITHUB_PUSH_LOCAL_PATH"] = config.get("OUTPUT_FILE", "")
    if not config.get("GITHUB_PUSH_REMOTE_PATH"):
        local_path = config.get("GITHUB_PUSH_LOCAL_PATH", "") or ""
        config["GITHUB_PUSH_REMOTE_PATH"] = os.path.basename(local_path) if local_path else ""

    return config

cfg = load_config()

# 提取所有配置变量
USE_GLOBAL_MODE = cfg["USE_GLOBAL_MODE"]
GLOBAL_TOP_N = cfg["GLOBAL_TOP_N"]
PER_COUNTRY_TOP_N = cfg["PER_COUNTRY_TOP_N"]
BANDWIDTH_CANDIDATES = cfg["BANDWIDTH_CANDIDATES"]
TCP_PROBES = cfg["TCP_PROBES"]
MIN_SUCCESS_RATE = cfg["MIN_SUCCESS_RATE"]
TIMEOUT = cfg["TIMEOUT"]
PROGRESS_PRINT_INTERVAL = cfg["PROGRESS_PRINT_INTERVAL"]
FILTER_COUNTRIES_ENABLED = cfg["FILTER_COUNTRIES_ENABLED"]
ALLOWED_COUNTRIES = cfg["ALLOWED_COUNTRIES"]
PRE_FILTER_BLOCKED_ENABLED = cfg["PRE_FILTER_BLOCKED_ENABLED"]
PRE_FILTER_BLOCKED_COUNTRIES = [c.upper() for c in cfg["PRE_FILTER_BLOCKED_COUNTRIES"]]
PRE_FILTER_PORT_ENABLED = cfg["PRE_FILTER_PORT_ENABLED"]
PRE_FILTER_PORTS = [str(p) for p in cfg["PRE_FILTER_PORTS"]]
ENABLE_WXPUSHER = cfg["ENABLE_WXPUSHER"]
WXPUSHER_APP_TOKEN = cfg["WXPUSHER_APP_TOKEN"]
WXPUSHER_UIDS = cfg["WXPUSHER_UIDS"]
WXPUSHER_API_URL = cfg["WXPUSHER_API_URL"]
NOTIFY_TIMEOUT = cfg["NOTIFY_TIMEOUT"]
NOTIFY_CONNECT_TIMEOUT = cfg["NOTIFY_CONNECT_TIMEOUT"]
CF_ENABLED = cfg["CF_ENABLED"]
CF_API_TOKEN = cfg["CF_API_TOKEN"]
CF_ZONE_ID = cfg["CF_ZONE_ID"]
CF_DNS_RECORD_NAME = cfg["CF_DNS_RECORD_NAME"]
CF_TTL = cfg["CF_TTL"]
CF_PROXIED = cfg["CF_PROXIED"]
CF_DNS_CONNECT_TIMEOUT = cfg["CF_DNS_CONNECT_TIMEOUT"]
CF_DNS_READ_TIMEOUT = cfg["CF_DNS_READ_TIMEOUT"]
DNS_RECORD_TYPE = cfg["DNS_RECORD_TYPE"]
ADDITIONAL_SOURCES = cfg["ADDITIONAL_SOURCES"]
FETCH_MAX_RETRIES = cfg["FETCH_MAX_RETRIES"]
FETCH_RETRY_DELAY = cfg["FETCH_RETRY_DELAY"]
FETCH_TIMEOUT = cfg["FETCH_TIMEOUT"]
FETCH_CONNECT_TIMEOUT = cfg["FETCH_CONNECT_TIMEOUT"]
OUTPUT_FILE = cfg["OUTPUT_FILE"]
ENABLE_LOGGING = cfg["ENABLE_LOGGING"]
LOG_FILE = cfg["LOG_FILE"]
TEST_AVAILABILITY = cfg["TEST_AVAILABILITY"]
AVAILABILITY_CHECK_API = cfg["AVAILABILITY_CHECK_API"]
AVAILABILITY_TIMEOUT = cfg["AVAILABILITY_TIMEOUT"]
AVAILABILITY_CONNECT_TIMEOUT = cfg["AVAILABILITY_CONNECT_TIMEOUT"]
AVAILABILITY_RETRY_MAX = cfg["AVAILABILITY_RETRY_MAX"]
AVAILABILITY_RETRY_DELAY = cfg["AVAILABILITY_RETRY_DELAY"]
FILTER_IPV6_AVAILABILITY = cfg["FILTER_IPV6_AVAILABILITY"]
FILTER_BLOCKED_COUNTRIES_ENABLED = cfg["FILTER_BLOCKED_COUNTRIES_ENABLED"]
BLOCKED_COUNTRIES = cfg["BLOCKED_COUNTRIES"]
DNS_IP_RISK_FILTER_ENABLED = cfg["DNS_IP_RISK_FILTER_ENABLED"]
DNS_IP_RISK_MAX_LEVEL = cfg["DNS_IP_RISK_MAX_LEVEL"]
DNS_UPDATE_TARGET_COUNT = cfg["DNS_UPDATE_TARGET_COUNT"]
BANDWIDTH_SIZE_MB = cfg["BANDWIDTH_SIZE_MB"]
BANDWIDTH_TIMEOUT = cfg["BANDWIDTH_TIMEOUT"]
BANDWIDTH_RETRY_MAX = cfg["BANDWIDTH_RETRY_MAX"]
BANDWIDTH_RETRY_DELAY = cfg["BANDWIDTH_RETRY_DELAY"]
BANDWIDTH_URL_TEMPLATE = cfg["BANDWIDTH_URL_TEMPLATE"]
BANDWIDTH_PROCESS_BUFFER = cfg["BANDWIDTH_PROCESS_BUFFER"]
BANDWIDTH_CONNECT_TIMEOUT = cfg["BANDWIDTH_CONNECT_TIMEOUT"]
MAX_WORKERS = cfg["MAX_WORKERS"]
AVAILABILITY_WORKERS = cfg["AVAILABILITY_WORKERS"]
FALLBACK_WORKERS = cfg["FALLBACK_WORKERS"]
BANDWIDTH_WORKERS = cfg["BANDWIDTH_WORKERS"]
DNS_UPDATE_MAX_RETRIES = cfg["DNS_UPDATE_MAX_RETRIES"]
DNS_UPDATE_RETRY_DELAY = cfg["DNS_UPDATE_RETRY_DELAY"]
GITHUB_SYNC_MAX_RETRIES = cfg["GITHUB_SYNC_MAX_RETRIES"]
GITHUB_SYNC_RETRY_DELAY = cfg["GITHUB_SYNC_RETRY_DELAY"]
GITHUB_PUSH_ENABLE = cfg["GITHUB_PUSH_ENABLE"]
GITHUB_PUSH_TOKEN = cfg["GITHUB_PUSH_TOKEN"]
GITHUB_PUSH_USERNAME = cfg["GITHUB_PUSH_USERNAME"]
GITHUB_PUSH_REPO = cfg["GITHUB_PUSH_REPO"]
GITHUB_PUSH_BRANCH = cfg["GITHUB_PUSH_BRANCH"]
GITHUB_PUSH_LOCAL_PATH = cfg["GITHUB_PUSH_LOCAL_PATH"]
GITHUB_PUSH_REMOTE_PATH = cfg["GITHUB_PUSH_REMOTE_PATH"]
GITHUB_PUSH_COMMIT_MESSAGE = cfg["GITHUB_PUSH_COMMIT_MESSAGE"]
GITHUB_PUSH_TIMEOUT = cfg["GITHUB_PUSH_TIMEOUT"]
AD_HEADER_ENABLED = cfg["AD_HEADER_ENABLED"]
AD_HEADER_LINES = cfg["AD_HEADER_LINES"]
AD_FOOTER_ENABLED = cfg["AD_FOOTER_ENABLED"]
AD_FOOTER_LINES = cfg["AD_FOOTER_LINES"]
AD_PERLINE_ENABLED = cfg["AD_PERLINE_ENABLED"]
AD_PERLINE_TEXT = cfg["AD_PERLINE_TEXT"]
IP_TXT_SHOW_BANDWIDTH = cfg["IP_TXT_SHOW_BANDWIDTH"]
IP_TXT_SHOW_LATENCY = cfg["IP_TXT_SHOW_LATENCY"]
CHECK_CHATGPT_ENABLED = cfg["CHECK_CHATGPT_ENABLED"]
CHATGPT_CHECK_TIMEOUT = cfg["CHATGPT_CHECK_TIMEOUT"]
CHATGPT_CHECK_WORKERS = cfg["CHATGPT_CHECK_WORKERS"]

BANDWIDTH_URL = BANDWIDTH_URL_TEMPLATE.format(bytes=int(BANDWIDTH_SIZE_MB * 1024 * 1024))

# cf_merge 配置
CF_MERGE_ENABLED = cfg["CF_MERGE_ENABLED"]
CF_MERGE_URLS = cfg["CF_MERGE_URLS"]
CF_MERGE_OUTPUT = cfg["CF_MERGE_OUTPUT"]
CF_MERGE_TIMEOUT = cfg["CF_MERGE_TIMEOUT"]
CF_MERGE_CONCURRENT = cfg["CF_MERGE_CONCURRENT"]
CF_MERGE_DEFAULT_PORT = cfg["CF_MERGE_DEFAULT_PORT"]
CF_MERGE_PUSH_ENABLE = cfg["CF_MERGE_PUSH_ENABLE"]
CF_MERGE_GITHUB_TOKEN = cfg["CF_MERGE_GITHUB_TOKEN"]
CF_MERGE_GITHUB_USERNAME = cfg["CF_MERGE_GITHUB_USERNAME"]
CF_MERGE_REPO_NAME = cfg["CF_MERGE_REPO_NAME"]
CF_MERGE_BRANCH = cfg["CF_MERGE_BRANCH"]
CF_MERGE_FILE_PATH = cfg["CF_MERGE_FILE_PATH"]
CF_MERGE_COMMIT_MESSAGE = cfg["CF_MERGE_COMMIT_MESSAGE"]


# ==================== 并发/内存自适应 ====================
if sys.platform != "win32":
    try:
        import resource
        soft_limit, _ = resource.getrlimit(resource.RLIMIT_NOFILE)
        safe_max = max(32, soft_limit // 2)
        if MAX_WORKERS > safe_max:
            print(f"⚠️ MAX_WORKERS={MAX_WORKERS} 超过文件描述符安全上限，已降低为 {safe_max}")
            MAX_WORKERS = safe_max
        AVAILABILITY_WORKERS = min(AVAILABILITY_WORKERS, safe_max)
        FALLBACK_WORKERS = min(FALLBACK_WORKERS, safe_max)
    except (ImportError, OSError, ValueError):
        pass


def _get_available_memory_mb():
    try:
        if sys.platform.startswith("linux"):
            with open("/proc/meminfo", "r") as f:
                for line in f:
                    if line.startswith("MemAvailable:"):
                        return int(line.split()[1]) // 1024
        try:
            import psutil
            return psutil.virtual_memory().available // (1024 * 1024)
        except ImportError:
            return None
    except (OSError, ValueError):
        return None


def _adjust_workers_by_memory(requested, per_worker_mb=5, min_workers=8):
    avail_mb = _get_available_memory_mb()
    if avail_mb is None:
        return requested
    safe = max(min_workers, (avail_mb // 2) // per_worker_mb)
    if requested > safe:
        print(f"⚠️ 可用内存约 {avail_mb}MB，将并发从 {requested} 降低为 {safe}")
        return safe
    return requested


MAX_WORKERS = _adjust_workers_by_memory(MAX_WORKERS, per_worker_mb=5)
AVAILABILITY_WORKERS = _adjust_workers_by_memory(AVAILABILITY_WORKERS, per_worker_mb=3)
FALLBACK_WORKERS = _adjust_workers_by_memory(FALLBACK_WORKERS, per_worker_mb=3)
BANDWIDTH_WORKERS = _adjust_workers_by_memory(BANDWIDTH_WORKERS, per_worker_mb=8, min_workers=2)


# ==================== 限流提交辅助 ====================
def bounded_submit(executor, fn, items, in_flight=None):
    """限流提交器：避免一次性提交所有任务导致 OOM"""
    max_workers = getattr(executor, "_max_workers", 32) or 32
    if in_flight is None:
        in_flight = max(max_workers * 4, 64)
    items_iter = iter(items)
    futures = {}
    for _ in range(in_flight):
        try:
            item = next(items_iter)
        except StopIteration:
            break
        futures[executor.submit(fn, item)] = item
    while futures:
        done, _ = wait(futures, return_when=FIRST_COMPLETED)
        for future in done:
            item = futures.pop(future)
            yield future, item
            try:
                next_item = next(items_iter)
                futures[executor.submit(fn, next_item)] = next_item
            except StopIteration:
                pass


# ==================== 通知 ====================
def send_wxpusher_notification(content, summary):
    if not ENABLE_WXPUSHER:
        return
    try:
        resp = requests.post(
            WXPUSHER_API_URL,
            json={"appToken": WXPUSHER_APP_TOKEN, "content": content, "summary": summary, "uids": WXPUSHER_UIDS},
            timeout=(NOTIFY_CONNECT_TIMEOUT, NOTIFY_TIMEOUT)
        )
        print("✅ 微信通知已发送" if resp.status_code == 200 else f"⚠️ 微信通知发送失败: {resp.status_code}")
    except (requests.RequestException, OSError) as e:
        print(f"⚠️ 微信通知异常: {e}")


# ==================== Phase 1: CF IP 合并下载 ====================
def is_valid_ipv4(ip: str) -> bool:
    return bool(IPV4_RE.match(ip.strip()))


def extract_region(url: str, line: str) -> str:
    """从 URL 或行内容中提取地区标签"""
    if match := REGION_RE.search(line):
        return match.group(1).lower()
    url_lower = url.lower()
    for region in REGIONS:
        if f"/{region}" in url_lower or f"_{region}" in url_lower or f"-{region}" in url_lower or region.upper() in url_lower:
            return region
    try:
        parsed = urllib.parse.urlparse(url)
        query_params = urllib.parse.parse_qs(parsed.query)
        if 'isp' in query_params and query_params['isp'][0].lower() in ['cm', 'ct', 'cu']:
            return 'cn'
    except Exception:
        pass
    return 'cf'


def parse_merge_line(url: str, line: str) -> Optional[str]:
    """解析单行，返回标准化格式: IP:端口#地区"""
    line = line.strip()
    if not line or line.startswith('#') or line.startswith('saas.') or line.startswith('bestcf.'):
        return None
    if match := LINE_RE.match(line):
        ip, port = match.group(1), match.group(2)
        if is_valid_ipv4(ip):
            return f"{ip}:{port}#{extract_region(url, line)}"
    if is_valid_ipv4(line):
        return f"{line}:{CF_MERGE_DEFAULT_PORT}#{extract_region(url, line)}"
    # 尝试分隔符解析
    parts = re.split(r'[#|,;\s\t]+', line)
    for part in parts:
        part = part.strip()
        if ':' in part and '.' in part:
            ip_port = part.split(':', 1)
            if len(ip_port) == 2 and ip_port[1].isdigit() and is_valid_ipv4(ip_port[0]):
                return f"{ip_port[0]}:{ip_port[1]}#{extract_region(url, line)}"
    return None


def fetch_merge_url(url: str) -> List[str]:
    """下载并解析单个 URL"""
    results = []
    print(f"📥 下载: {url}")
    try:
        req = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0 cf-merge/1.0'})
        with urllib.request.urlopen(req, timeout=CF_MERGE_TIMEOUT, context=SSL_CONTEXT) as resp:
            content = resp.read()
            encoding = resp.headers.get_content_charset() or 'utf-8'
            try:
                text = content.decode(encoding)
            except UnicodeDecodeError:
                text = content.decode('utf-8', errors='ignore')
            for line in text.splitlines():
                if entry := parse_merge_line(url, line):
                    results.append(entry)
    except urllib.error.HTTPError as e:
        print(f"❌ HTTP错误 {url}: {e.code}")
    except urllib.error.URLError as e:
        print(f"❌ 网络错误 {url}: {e.reason}")
    except Exception as e:
        print(f"❌ 错误 {url}: {type(e).__name__}: {e}")
    return results


def merge_and_dedup(entries: List[str]) -> List[str]:
    """去重 + 按地区+IP排序"""
    seen: Set[str] = set()
    result = []
    for entry in entries:
        if entry not in seen:
            seen.add(entry)
            result.append(entry)
    result.sort(key=lambda e: (e.split('#', 1)[1] if '#' in e else 'cf', e))
    return result


def _github_api_upload(token: str, username: str, repo: str, branch: str,
                       remote_path: str, content_bytes: bytes,
                       commit_message: str, timeout: int):
    """通过 GitHub Contents API 上传文件内容

    返回 (success: bool, message: str, skipped: bool)
    skipped=True 表示远程内容与本地一致，无需推送（仍视为成功）
    """
    import base64
    import hashlib

    if not token or token.startswith("ghp_xxx") or token.startswith("your_"):
        return False, "未配置有效的 GitHub Token", False
    if not username or not repo or not branch or not remote_path:
        return False, "GitHub 仓库 / 分支 / 远程路径配置不完整", False

    api_url = f"https://api.github.com/repos/{username}/{repo}/contents/{urllib.parse.quote(remote_path)}"
    headers = {
        "Accept": "application/vnd.github+json",
        "Authorization": f"Bearer {token}",
        "X-GitHub-Api-Version": "2022-11-28",
        "User-Agent": "cfnb-github-sync"
    }

    # 1) 查询远程文件 SHA
    sha = None
    try:
        req = urllib.request.Request(
            f"{api_url}?ref={urllib.parse.quote(branch)}", headers=headers
        )
        with urllib.request.urlopen(req, timeout=timeout, context=SSL_CONTEXT) as resp:
            sha = json.loads(resp.read().decode('utf-8')).get('sha')
    except urllib.error.HTTPError as e:
        if e.code != 404:
            return False, f"查询远程文件失败: HTTP {e.code}", False
    except Exception as e:
        return False, f"查询远程文件异常: {e}", False

    # 2) 计算本地内容的 git blob SHA1，远程一致则跳过推送
    try:
        blob_hash = hashlib.sha1(
            b"blob " + str(len(content_bytes)).encode() + b"\0" + content_bytes
        ).hexdigest()
        if sha and sha == blob_hash:
            return True, "远程内容已是最新，跳过推送", True
    except Exception:
        pass

    # 3) PUT 上传
    content_b64 = base64.b64encode(content_bytes).decode('ascii')
    payload = {"message": commit_message, "content": content_b64, "branch": branch}
    if sha:
        payload["sha"] = sha

    data = json.dumps(payload).encode('utf-8')
    headers["Content-Type"] = "application/json"
    req = urllib.request.Request(api_url, data=data, headers=headers, method='PUT')
    try:
        with urllib.request.urlopen(req, timeout=timeout, context=SSL_CONTEXT) as resp:
            result = json.loads(resp.read().decode('utf-8'))
            commit_sha = result.get('commit', {}).get('sha', 'N/A')
            return True, f"推送成功 commit: {commit_sha[:7]}", False
    except urllib.error.HTTPError as e:
        error_body = e.read().decode('utf-8', errors='ignore')
        return False, f"推送失败 (HTTP {e.code}): {error_body[:200]}", False
    except Exception as e:
        return False, f"推送异常: {e}", False


def github_push_merged(content_lines: List[str]) -> bool:
    """通过 GitHub Contents API 推送合并后的 CF IP 文件"""
    if not CF_MERGE_PUSH_ENABLE:
        print("⏭️  跳过合并文件推送")
        return True

    content_bytes = ('\n'.join(content_lines) + '\n').encode('utf-8')
    print(f"📤 推送合并文件 ({len(content_lines)} 条) ...")

    success, msg, skipped = _github_api_upload(
        token=CF_MERGE_GITHUB_TOKEN,
        username=CF_MERGE_GITHUB_USERNAME,
        repo=CF_MERGE_REPO_NAME,
        branch=CF_MERGE_BRANCH,
        remote_path=CF_MERGE_FILE_PATH,
        content_bytes=content_bytes,
        commit_message=CF_MERGE_COMMIT_MESSAGE,
        timeout=CF_MERGE_TIMEOUT,
    )
    if success:
        icon = "⏭️ " if skipped else "🎉"
        print(f"{icon} {msg}")
        return True
    print(f"❌ {msg}")
    return False


def run_cf_merge() -> List[str]:
    """执行 Phase 1: 多源下载合并去重，推送到 GitHub，返回合并后的节点列表"""
    if not CF_MERGE_ENABLED:
        print("⏭️  CF IP 合并已禁用")
        return []

    print("=" * 60)
    print("🚀 Phase 1: CF IP 多源下载合并")
    print(f"📊 数据源: {len(CF_MERGE_URLS)} 个 | 并发: {CF_MERGE_CONCURRENT}")
    print("=" * 60)

    all_results = []
    with ThreadPoolExecutor(max_workers=CF_MERGE_CONCURRENT) as executor:
        future_to_url = {executor.submit(fetch_merge_url, url): url for url in CF_MERGE_URLS}
        for future in as_completed(future_to_url):
            all_results.extend(future.result())

    print(f"\n🔍 原始条目: {len(all_results)}")
    sorted_entries = merge_and_dedup(all_results)
    print(f"✅ 去重后: {len(sorted_entries)} 条")

    # 写入本地文件
    with open(CF_MERGE_OUTPUT, 'w', encoding='utf-8') as f:
        for entry in sorted_entries:
            f.write(entry + '\n')
    print(f"📁 已保存: {CF_MERGE_OUTPUT}")

    # 地区统计
    region_count: defaultdict = defaultdict(int)
    for entry in sorted_entries:
        region_count[entry.split('#', 1)[1] if '#' in entry else 'cf'] += 1
    print("\n🌍 地区分布:")
    for region, count in sorted(region_count.items(), key=lambda x: -x[1]):
        print(f"   {region.upper()}: {count}")

    # 推送到 GitHub
    github_push_merged(sorted_entries)
    return sorted_entries


# ==================== Phase 2: IP 筛选测速 (原 main.py 核心逻辑) ====================

# IP 风险等级
RISK_LEVEL_ORDER = {"极度纯净": 0, "纯净": 1, "轻微风险": 2, "高风险": 3, "极度危险": 4}


def get_ip_risk_level(ip):
    url = f"https://api.ipapi.is/?q={ip}"
    try:
        resp = requests.get(url, timeout=10)
        resp.raise_for_status()
        data = resp.json()
    except (requests.RequestException, ValueError, OSError):
        return "未知"

    def extract_score(score_str):
        if not score_str:
            return 0.0
        match = re.match(r"([\d.]+)\s*\(([^)]+)\)", str(score_str).strip())
        return float(match.group(1)) if match else float(score_str) if score_str else 0.0

    company = extract_score(data.get("company", {}).get("abuser_score"))
    asn = extract_score(data.get("asn", {}).get("abuser_score"))
    base_score = ((company + asn) / 2) * 5

    risk_count = sum(1 for k in ["is_crawler", "is_proxy", "is_vpn", "is_tor", "is_abuser"] if data.get(k, False))
    final_score = base_score + risk_count * 0.15
    if data.get("is_bogon", False):
        final_score += 1.0

    percentage = final_score * 100
    if percentage >= 100: return "极度危险"
    elif percentage >= 20: return "高风险"
    elif percentage >= 5: return "轻微风险"
    elif percentage >= 0.25: return "纯净"
    else: return "极度纯净"


# ChatGPT 支持检测
def check_chatgpt_support_single(node_str):
    m = IP_PORT_PATTERN.match(node_str)
    if not m:
        return (node_str, False)
    ip, port = m.group(1), m.group(2)
    null_device = "NUL" if sys.platform == "win32" else "/dev/null"
    curl_cmd = [
        "curl", "-s", "-o", null_device, "-w", "%{http_code}",
        "--resolve", f"api.openai.com:{port}:{ip}",
        "--connect-timeout", str(CHATGPT_CHECK_TIMEOUT),
        "--max-time", str(CHATGPT_CHECK_TIMEOUT),
        "--insecure", f"https://api.openai.com:{port}/v1/models"
    ]
    try:
        result = subprocess.run(curl_cmd, capture_output=True, text=True, timeout=CHATGPT_CHECK_TIMEOUT + 2)
        if result.returncode == 0 and result.stdout.strip():
            return (node_str, int(result.stdout.strip()) == 401)
    except (subprocess.TimeoutExpired, subprocess.SubprocessError, OSError, ValueError):
        pass
    return (node_str, False)


def check_chatgpt_batch(nodes):
    if not CHECK_CHATGPT_ENABLED or not nodes or not shutil.which("curl"):
        return set()
    print(f"\n开始 ChatGPT 支持检测（{len(nodes)} 个节点）...")
    supported = set()
    completed = 0
    total = len(nodes)
    last_print = time.time()
    with ThreadPoolExecutor(max_workers=CHATGPT_CHECK_WORKERS) as executor:
        for future, _ in bounded_submit(executor, check_chatgpt_support_single, nodes):
            completed += 1
            try:
                node_str, ok = future.result()
                if ok:
                    supported.add(node_str)
            except Exception:
                pass
            now = time.time()
            if now - last_print >= PROGRESS_PRINT_INTERVAL or completed == total:
                print(f"\r[ChatGPT检测] {completed}/{total} ({(completed/total)*100:.1f}%) 支持：{len(supported)}", end="", flush=True)
                last_print = now
    print(f"\n✅ ChatGPT 检测完成：{len(supported)}/{total} 支持")
    return supported


# 自适应数据源解析
def extract_country_code(label):
    label = label.strip()
    if not label:
        return None
    tokens = re.split(r'[\s,;|/]+', label)
    for token in tokens:
        token_cleaned = re.sub(r'^[\d\s\-_.|#]+', '', token.strip())
        if re.match(r'^[A-Z]{2}$', token_cleaned):
            return token_cleaned
    for token in tokens:
        token_cleaned = re.sub(r'^[\d\s\-_.|#]+', '', token)
        token_no_emoji = re.sub(r'[\U0001F1E6-\U0001F1FF]', '', token_cleaned).strip()
        cn_match = re.match(r'^([\u4e00-\u9fff（）()]+)\d*$', token_no_emoji)
        if cn_match:
            code = CN_TO_CODE.get(cn_match.group(1).strip())
            if code:
                return code
    emoji_chars = [c for c in label if '\U0001F1E6' <= c <= '\U0001F1FF']
    if len(emoji_chars) >= 2 and len(emoji_chars) % 2 == 0:
        first = ord(emoji_chars[0]) - 0x1F1E6
        second = ord(emoji_chars[1]) - 0x1F1E6
        if 0 <= first <= 25 and 0 <= second <= 25:
            return chr(first + ord('A')) + chr(second + ord('A'))
    return None


@lru_cache(maxsize=10000)
def _query_country(ip, port):
    try:
        resp = requests.get(AVAILABILITY_CHECK_API, params={"proxyip": f"{ip}:{port}"},
                           timeout=(AVAILABILITY_CONNECT_TIMEOUT, AVAILABILITY_TIMEOUT))
        if resp.status_code == 200:
            data = resp.json()
            probe = (data or {}).get("probe_results") or {}
            ipv4 = probe.get("ipv4") or {}
            country = (ipv4.get("exit") or {}).get("country") or ""
            if country and len(country) == 2:
                return country.upper()
    except (requests.RequestException, ValueError, OSError, AttributeError, TypeError):
        pass
    return None


def _resolve_countries_batch(ipports):
    results = {}
    total = len(ipports)
    completed = 0
    last_print = time.time()

    def worker(ipport):
        ip, port = ipport.rsplit(':', 1)
        return ipport, _query_country(ip, port)

    with ThreadPoolExecutor(max_workers=FALLBACK_WORKERS) as executor:
        for future, item in bounded_submit(executor, worker, ipports):
            try:
                ipport, code = future.result()
                results[ipport] = code
            except Exception:
                results[item] = None
            completed += 1
            now = time.time()
            if now - last_print >= PROGRESS_PRINT_INTERVAL or completed == total:
                print(f"\r[备用API查询] {completed}/{total} ({(completed/total)*100:.1f}%)", end="", flush=True)
                last_print = now
    if total > 0:
        print()
    return results


def _parse_json_nodes(data, depth=0, max_depth=64):
    if depth > max_depth:
        return []
    nodes = []
    if isinstance(data, list):
        for item in data:
            nodes.extend(_parse_json_nodes(item, depth + 1, max_depth))
    elif isinstance(data, dict):
        for key in ('nodes', 'data', 'result', 'list'):
            if key in data and isinstance(data[key], list):
                nodes.extend(_parse_json_nodes(data[key], depth + 1, max_depth))
                break
        ip = data.get('ip') or data.get('host')
        port = data.get('port')
        code = data.get('country') or data.get('cc')
        if ip and port and code:
            nodes.append(f"{ip}:{port}#{code.upper()}")
    elif isinstance(data, str):
        nodes.extend(_parse_text_nodes(data))
    return nodes


def _parse_text_nodes(text):
    nodes = []
    pending = []
    for token in text.split():
        if '#' not in token:
            continue
        try:
            ipport, label = token.split('#', 1)
        except ValueError:
            continue
        if ipport.startswith('[') or not re.match(r'^\d+\.\d+\.\d+\.\d+:\d+$', ipport):
            continue
        code = extract_country_code(label)
        if code:
            nodes.append(f"{ipport}#{code}")
        else:
            pending.append(ipport)
    if pending:
        print(f"{len(pending)} 个标签未能识别，通过 API 查询国家...")
        resolved = _resolve_countries_batch(pending)
        for ipport, code in resolved.items():
            if code:
                nodes.append(f"{ipport}#{code}")
    return nodes


def parse_adaptive(text):
    text = text.strip()
    if not text:
        return []
    if text.startswith('{') or text.startswith('['):
        try:
            return _parse_json_nodes(json.loads(text))
        except (json.JSONDecodeError, Exception):
            pass
    return _parse_text_nodes(text)


FETCH_MAX_BYTES = 200 * 1024 * 1024


def _read_response_stream(resp, max_bytes=FETCH_MAX_BYTES, chunk_size=64 * 1024):
    chunks = []
    total = 0
    encoding = resp.encoding or resp.apparent_encoding or "utf-8"
    for chunk in resp.iter_content(chunk_size=chunk_size, decode_unicode=False):
        if not chunk:
            continue
        total += len(chunk)
        if total > max_bytes:
            raise ValueError(f"响应体超过上限 {max_bytes // (1024*1024)}MB")
        chunks.append(chunk)
    raw = b"".join(chunks)
    chunks.clear()
    try:
        return raw.decode(encoding, errors="replace")
    finally:
        del raw


def fetch_additional_source(url):
    if not url:
        return []
    for attempt in range(1, FETCH_MAX_RETRIES + 1):
        resp = None
        try:
            print(f"正在请求数据源 {url} (尝试 {attempt}/{FETCH_MAX_RETRIES}) ...")
            resp = requests.get(url, timeout=(FETCH_CONNECT_TIMEOUT, FETCH_TIMEOUT), stream=True)
            resp.raise_for_status()
            text = _read_response_stream(resp)
            nodes = parse_adaptive(text)
            del text
            gc.collect()
            print(f"从 {url} 解析出 {len(nodes)} 个节点。")
            return nodes
        except (requests.RequestException, ValueError, OSError) as e:
            print(f"请求失败 ({url}): {e}")
            if attempt < FETCH_MAX_RETRIES:
                time.sleep(FETCH_RETRY_DELAY)
            else:
                return []
        finally:
            if resp:
                resp.close()
    return []


# ==================== 核心测试、筛选、测速 ====================
def test_tcp_latency(ip, port, timeout=TIMEOUT, probes=TCP_PROBES):
    min_latency = float("inf")
    success = 0
    for _ in range(probes):
        try:
            start = time.time()
            with socket.socket(socket.AF_INET, socket.SOCK_STREAM) as sock:
                sock.settimeout(timeout)
                sock.connect((ip, int(port)))
            latency = time.time() - start
            if latency < min_latency:
                min_latency = latency
            success += 1
        except (socket.error, OSError):
            continue
    return min_latency, success


def test_node(node_str):
    m = NODE_PATTERN.match(node_str)
    if not m:
        return None
    ip, port, country = m.groups()
    min_lat, success = test_tcp_latency(ip, port)
    if success == 0 or (success / TCP_PROBES) < MIN_SUCCESS_RATE:
        return None
    return (node_str, min_lat, country, success)


def check_availability(node_str):
    m = IP_PORT_PATTERN.match(node_str)
    if not m:
        return (node_str, False, "unknown", {})
    ip, port = m.group(1), m.group(2)
    try:
        resp = requests.get(AVAILABILITY_CHECK_API, params={"proxyip": f"{ip}:{port}"},
                           timeout=(AVAILABILITY_CONNECT_TIMEOUT, AVAILABILITY_TIMEOUT))
        if resp.status_code == 200:
            data = resp.json()
            if data.get("success") is True:
                stack = data.get("inferred_stack", "unknown")
                probe = data.get("probe_results", {}).get("ipv6") or data.get("probe_results", {}).get("ipv4") or {}
                return (node_str, True, stack, probe.get("exit", {}))
    except (requests.RequestException, ValueError, OSError):
        pass
    return (node_str, False, "unknown", {})


def availability_filter_with_retry(candidates):
    if not TEST_AVAILABILITY or not candidates:
        return candidates, {}, {}

    for attempt in range(1, AVAILABILITY_RETRY_MAX + 1):
        print(f"\n[可用性检测] 第 {attempt} 轮...")
        passed, ip_info, exit_details = [], {}, {}
        completed = 0
        total = len(candidates)
        last_print = time.time()

        with ThreadPoolExecutor(max_workers=AVAILABILITY_WORKERS) as executor:
            for future, _ in bounded_submit(executor, check_availability, candidates):
                completed += 1
                try:
                    node_str, ok, stack, exit_info = future.result()
                    if ok:
                        passed.append(node_str)
                        ip_info[node_str] = stack
                        exit_details[node_str] = exit_info
                except Exception:
                    pass
                now = time.time()
                if now - last_print >= PROGRESS_PRINT_INTERVAL or completed == total:
                    print(f"\r[可用性检测] {completed}/{total} ({(completed/total)*100:.1f}%) 通过：{len(passed)}", end="", flush=True)
                    last_print = now
        print()

        if passed:
            print(f"✅ 可用性检测通过 {len(passed)} 个节点")
            return passed, ip_info, exit_details
        if attempt < AVAILABILITY_RETRY_MAX:
            print(f"⚠️ 本轮通过率为 0%，等待 {AVAILABILITY_RETRY_DELAY}s 后重试...")
            time.sleep(AVAILABILITY_RETRY_DELAY)

    print(f"❌ 可用性检测 {AVAILABILITY_RETRY_MAX} 轮后仍无通过。")
    send_wxpusher_notification(content="可用性检测全部失败，使用原候选列表继续。", summary="可用性检测全部失败")
    return candidates, {}, {}


def measure_bandwidth_curl(node_str):
    m = IP_PORT_PATTERN.match(node_str)
    if not m:
        return (node_str, 0)
    ip, port = m.group(1), m.group(2)
    null_device = "NUL" if sys.platform == "win32" else "/dev/null"
    curl_cmd = [
        "curl", "-s", "-o", null_device, "-w", "%{size_download} %{time_total}",
        "--resolve", f"speed.cloudflare.com:{port}:{ip}",
        "--connect-timeout", str(BANDWIDTH_CONNECT_TIMEOUT),
        "--max-time", str(BANDWIDTH_TIMEOUT),
        "--insecure", BANDWIDTH_URL
    ]
    try:
        result = subprocess.run(curl_cmd, capture_output=True, text=True, timeout=BANDWIDTH_TIMEOUT + BANDWIDTH_PROCESS_BUFFER)
        if result.returncode == 0 and result.stdout.strip():
            parts = result.stdout.strip().split()
            if len(parts) >= 2:
                size_bytes, time_total = float(parts[0]), float(parts[1])
                if time_total > 0 and size_bytes > 0:
                    return (node_str, (size_bytes * 8) / (time_total * 1000 * 1000))
    except (subprocess.TimeoutExpired, subprocess.SubprocessError, OSError, ValueError):
        pass
    return (node_str, 0)


def bandwidth_filter(candidates):
    if not candidates or not shutil.which("curl"):
        return []
    print(f"\n开始带宽测速（{len(candidates)} 个节点，并发 {BANDWIDTH_WORKERS}）...")
    results = []
    completed = 0
    total = len(candidates)
    last_print = time.time()
    with ThreadPoolExecutor(max_workers=BANDWIDTH_WORKERS) as executor:
        for future, _ in bounded_submit(executor, measure_bandwidth_curl, candidates):
            completed += 1
            try:
                node, speed = future.result()
                if speed > 0:
                    results.append((node, speed))
            except Exception:
                pass
            now = time.time()
            if now - last_print >= PROGRESS_PRINT_INTERVAL or completed == total:
                print(f"\r[带宽测速] {completed}/{total} ({(completed/total)*100:.1f}%)", end="", flush=True)
                last_print = now
    print()
    results.sort(key=lambda x: x[1], reverse=True)
    return results


# ==================== DNS 更新 + GitHub 同步 ====================
def batch_update_cloudflare_dns(ip_list, ip_info=None, full_bw_results=None, target_count=None, latency_map=None):
    if not CF_ENABLED:
        print("Cloudflare DNS 批量更新未启用。")
        return
    if target_count is None:
        target_count = DNS_UPDATE_TARGET_COUNT

    dns_ip_list, dns_node_list = [], []
    filtered_by_port = filtered_by_ipv6 = filtered_by_country = filtered_by_risk = 0
    risk_fallback_ip_list, risk_fallback_node_list = [], []

    if full_bw_results and ip_info:
        blocked_set = {c.upper() for c in BLOCKED_COUNTRIES} if FILTER_BLOCKED_COUNTRIES_ENABLED else set()
        for node_str, speed in full_bw_results:
            if ':' in node_str:
                port = node_str.split(':')[1].split('#')[0]
                if port != '443':
                    filtered_by_port += 1
                    continue
            if FILTER_IPV6_AVAILABILITY and ip_info.get(node_str, "unknown") == "ipv6_only":
                filtered_by_ipv6 += 1
                continue
            if blocked_set and '#' in node_str and node_str.split('#')[-1].upper() in blocked_set:
                filtered_by_country += 1
                continue

            pure_ip = node_str.split(':')[0]
            if DNS_IP_RISK_FILTER_ENABLED:
                risk_fallback_ip_list.append(pure_ip)
                risk_fallback_node_list.append(node_str)
                risk_level = get_ip_risk_level(pure_ip)
                if risk_level == "未知" or RISK_LEVEL_ORDER.get(risk_level, 99) > RISK_LEVEL_ORDER.get(DNS_IP_RISK_MAX_LEVEL, 2):
                    filtered_by_risk += 1
                    continue

            dns_ip_list.append(pure_ip)
            dns_node_list.append(node_str)
            if len(dns_ip_list) >= target_count:
                break

        if DNS_IP_RISK_FILTER_ENABLED and not dns_ip_list and filtered_by_risk > 0:
            send_wxpusher_notification(content="风险等级检测全部失败，已回退。", summary="风险等级检测全部失败")
            dns_ip_list = risk_fallback_ip_list[:target_count]
            dns_node_list = risk_fallback_node_list[:target_count]

    if not dns_ip_list:
        if ip_list:
            dns_ip_list = ip_list
            dns_node_list = ip_list
        else:
            print("没有可用的 IP 用于 DNS 更新。")
            return

    # 去重
    seen = set()
    unique_ips, unique_nodes = [], []
    for ip, node in zip(dns_ip_list, dns_node_list):
        if ip not in seen:
            seen.add(ip)
            unique_ips.append(ip)
            unique_nodes.append(node)
    dns_ip_list, dns_node_list = unique_ips, unique_nodes

    print(f"\n准备将 {len(dns_ip_list)} 个 IP 更新到 Cloudflare DNS:")
    speed_map = {node: speed for node, speed in full_bw_results} if full_bw_results else {}
    for i, (ip, node) in enumerate(zip(dns_ip_list, dns_node_list), 1):
        speed = speed_map.get(node, 0)
        lat_ms = latency_map.get(node, float('inf')) * 1000 if latency_map and node in latency_map else float('inf')
        if lat_ms != float('inf'):
            print(f"{i}. {node} {speed:.2f} Mbps {lat_ms:.2f} ms")
        else:
            print(f"{i}. {ip} {speed:.2f} Mbps")

    headers = {"Authorization": f"Bearer {CF_API_TOKEN}", "Content-Type": "application/json"}

    for attempt in range(1, DNS_UPDATE_MAX_RETRIES + 1):
        try:
            list_url = f"https://api.cloudflare.com/client/v4/zones/{CF_ZONE_ID}/dns_records"
            response = requests.get(list_url, headers=headers,
                                   params={"type": DNS_RECORD_TYPE, "name": CF_DNS_RECORD_NAME},
                                   timeout=(CF_DNS_CONNECT_TIMEOUT, CF_DNS_READ_TIMEOUT))
            response.raise_for_status()
            result = response.json()
            if not result.get('success'):
                raise RuntimeError(f"查询失败: {result.get('errors')}")

            existing_records = result.get('result', [])
            deletes = [{"id": rec["id"]} for rec in existing_records]
            posts = [{"name": CF_DNS_RECORD_NAME, "type": DNS_RECORD_TYPE, "content": ip, "ttl": CF_TTL, "proxied": CF_PROXIED} for ip in dns_ip_list]

            batch_url = f"https://api.cloudflare.com/client/v4/zones/{CF_ZONE_ID}/dns_records/batch"
            response = requests.post(batch_url, headers=headers, json={"deletes": deletes, "posts": posts},
                                    timeout=(CF_DNS_CONNECT_TIMEOUT, CF_DNS_READ_TIMEOUT))
            response.raise_for_status()
            if not response.json().get('success'):
                raise RuntimeError(f"批量更新失败: {response.json().get('errors')}")

            print(f"✅ DNS 更新成功！{CF_DNS_RECORD_NAME} → {len(dns_ip_list)} 个 IP")
            return
        except (requests.RequestException, ValueError, OSError, RuntimeError) as e:
            print(f"[尝试 {attempt}/{DNS_UPDATE_MAX_RETRIES}] DNS 更新出错: {e}")
            if attempt < DNS_UPDATE_MAX_RETRIES:
                time.sleep(DNS_UPDATE_RETRY_DELAY)
            else:
                send_wxpusher_notification(content=f"DNS 更新失败: {e}", summary="DNS 更新失败")


def sync_to_github():
    """通过 GitHub Contents API 推送 OUTPUT_FILE 到 GitHub"""
    if not GITHUB_PUSH_ENABLE:
        print("⏭️  GitHub 推送已禁用，跳过")
        return

    local_path = GITHUB_PUSH_LOCAL_PATH or OUTPUT_FILE
    remote_path = GITHUB_PUSH_REMOTE_PATH or os.path.basename(local_path)

    if not os.path.isabs(local_path):
        local_path = os.path.join(os.path.dirname(os.path.abspath(__file__)), local_path)

    if not os.path.exists(local_path):
        print(f"⚠️ 未找到本地文件 {local_path}，跳过 GitHub 同步")
        return

    try:
        with open(local_path, "rb") as f:
            content_bytes = f.read()
    except OSError as e:
        print(f"❌ 读取 {local_path} 失败: {e}")
        return

    last_msg = ""
    for attempt in range(1, GITHUB_SYNC_MAX_RETRIES + 1):
        print(f"\n📤 推送 {os.path.basename(local_path)} 到 GitHub "
              f"({GITHUB_PUSH_USERNAME}/{GITHUB_PUSH_REPO}@{GITHUB_PUSH_BRANCH}:{remote_path}) "
              f"尝试 {attempt}/{GITHUB_SYNC_MAX_RETRIES} ...")
        success, msg, skipped = _github_api_upload(
            token=GITHUB_PUSH_TOKEN,
            username=GITHUB_PUSH_USERNAME,
            repo=GITHUB_PUSH_REPO,
            branch=GITHUB_PUSH_BRANCH,
            remote_path=remote_path,
            content_bytes=content_bytes,
            commit_message=GITHUB_PUSH_COMMIT_MESSAGE,
            timeout=GITHUB_PUSH_TIMEOUT,
        )
        last_msg = msg
        if success:
            icon = "⏭️ " if skipped else "✅"
            print(f"{icon} {msg}")
            return
        print(f"❌ {msg}")
        if attempt < GITHUB_SYNC_MAX_RETRIES:
            time.sleep(GITHUB_SYNC_RETRY_DELAY)

    send_wxpusher_notification(
        content=f"GitHub 推送 {os.path.basename(local_path)} 失败，已重试 "
                f"{GITHUB_SYNC_MAX_RETRIES} 次。最后错误: {last_msg}",
        summary="GitHub 推送失败"
    )


def write_ip_txt(final_nodes, output_file, speed_map=None, latency_map=None, chatgpt_set=None):
    with open(output_file, "w", encoding="utf-8") as f:
        if AD_HEADER_ENABLED:
            for line in AD_HEADER_LINES:
                f.write(line + "\n")
        for node in final_nodes:
            line = node
            if chatgpt_set and node in chatgpt_set:
                line += " [ChatGPT]"
            if IP_TXT_SHOW_BANDWIDTH and speed_map and node in speed_map:
                line += f" {speed_map[node]:.2f} Mbps"
            if IP_TXT_SHOW_LATENCY and latency_map and node in latency_map:
                line += f" {latency_map[node]*1000:.2f} ms"
            if AD_PERLINE_ENABLED and AD_PERLINE_TEXT:
                line += AD_PERLINE_TEXT
            f.write(line + "\n")
        if AD_FOOTER_ENABLED:
            for line in AD_FOOTER_LINES:
                f.write(line + "\n")


# ==================== 主流程 ====================
def main():
    # ===== Phase 1: CF IP 多源合并 =====
    merged_nodes = run_cf_merge()

    # ===== Phase 2: IP 筛选测速 =====
    print("\n" + "=" * 60)
    print("🚀 Phase 2: IP 筛选测速")
    print("=" * 60)

    mode_str = f"全局最优{GLOBAL_TOP_N}个" if USE_GLOBAL_MODE else f"每个国家最优{PER_COUNTRY_TOP_N}个"
    print(f"模式：{mode_str} | TCP探测 {TCP_PROBES} 次 | 最低成功率 {MIN_SUCCESS_RATE*100:.0f}%")
    print(f"可用性筛选：{'启用' if TEST_AVAILABILITY else '禁用'} | ChatGPT检测：{'启用' if CHECK_CHATGPT_ENABLED else '禁用'}")

    # 从 ADDITIONAL_SOURCES 加载数据源（这里会拉取 Phase 1 推送的合并文件）
    nodes = []
    for source in ADDITIONAL_SOURCES:
        if not source.get("enabled", True):
            continue
        url = source.get("url")
        if not url:
            continue
        v2_nodes = fetch_additional_source(url)
        if v2_nodes:
            seen = {n.split('#')[0] for n in nodes}
            for n in v2_nodes:
                key = n.split('#')[0]
                if key not in seen:
                    seen.add(key)
                    nodes.append(n)

    # 如果 Phase 1 有结果且 ADDITIONAL_SOURCES 未包含，直接使用合并结果
    if not nodes and merged_nodes:
        print("使用 Phase 1 合并结果作为数据源...")
        nodes = merged_nodes[:]

    print(f"合并后总计 {len(nodes)} 个节点。")

    # 前置端口过滤
    if PRE_FILTER_PORT_ENABLED:
        before = len(nodes)
        nodes = [n for n in nodes if n.split(':')[1].split('#')[0] in PRE_FILTER_PORTS]
        print(f"前置端口过滤：{before} -> {len(nodes)}")
        if not nodes:
            print("⚠️ 过滤后无节点，退出。")
            sys.exit(0)

    # 前置黑名单过滤
    if PRE_FILTER_BLOCKED_ENABLED and PRE_FILTER_BLOCKED_COUNTRIES:
        before = len(nodes)
        blocked_set = set(PRE_FILTER_BLOCKED_COUNTRIES)
        nodes = [n for n in nodes if n.split('#')[-1].upper() not in blocked_set]
        print(f"前置黑名单过滤：{before} -> {len(nodes)}")
        if not nodes:
            print("⚠️ 过滤后无节点，退出。")
            sys.exit(0)

    if not nodes:
        print("没有有效节点，退出。")
        sys.exit(1)

    # 国家白名单过滤
    if FILTER_COUNTRIES_ENABLED and ALLOWED_COUNTRIES:
        before = len(nodes)
        allowed_set = {c.upper() for c in ALLOWED_COUNTRIES}
        nodes = [n for n in nodes if '#' in n and n.split('#')[1].upper() in allowed_set]
        print(f"国家白名单过滤：{before} -> {len(nodes)}")
        if not nodes:
            sys.exit(0)

    # TCP 连接测试
    total = len(nodes)
    print(f"\n开始 TCP 测试（超时 {TIMEOUT}s，并发 {MAX_WORKERS}）...")
    results = []
    completed = 0
    last_print = time.time()
    with ThreadPoolExecutor(max_workers=MAX_WORKERS) as executor:
        for future, _ in bounded_submit(executor, test_node, nodes):
            completed += 1
            try:
                res = future.result()
                if res:
                    results.append(res)
            except Exception:
                pass
            now = time.time()
            if now - last_print >= PROGRESS_PRINT_INTERVAL or completed == total:
                print(f"\r进度：{completed}/{total} ({(completed/total)*100:.1f}%)", end="", flush=True)
                last_print = now
    print("\nTCP 测试完成！")

    if not results:
        print("没有通过筛选的节点。")
        sys.exit(0)

    nodes = None
    gc.collect()

    results.sort(key=lambda x: (-x[3], x[1]))
    latency_map = {node: lat for node, lat, _, _ in results}

    # 选取候选池
    if USE_GLOBAL_MODE:
        candidates = [node for node, _, _, _ in results[:BANDWIDTH_CANDIDATES]]
    else:
        country_nodes = defaultdict(list)
        for node_str, lat, country, succ in results:
            country_nodes[country].append((node_str, lat, succ))
        total_countries = len(country_nodes)
        base_limit = max(1, BANDWIDTH_CANDIDATES // total_countries)
        candidates = []
        for country, nodes_in_c in country_nodes.items():
            nodes_sorted = sorted(nodes_in_c, key=lambda x: (-x[2], x[1]))
            for node_str, _, _ in nodes_sorted[:base_limit]:
                candidates.append(node_str)

    if not candidates:
        print("没有候选节点，退出。")
        sys.exit(0)

    # 可用性筛选
    candidates_after, avail_ip_info, _ = availability_filter_with_retry(candidates)

    # 带宽测速
    bw_results = []
    if shutil.which("curl"):
        for attempt in range(1, BANDWIDTH_RETRY_MAX + 1):
            bw_results = bandwidth_filter(candidates_after)
            if bw_results:
                break
            if attempt < BANDWIDTH_RETRY_MAX:
                time.sleep(BANDWIDTH_RETRY_DELAY)

    # 最终选择
    speed_map = {}
    if not bw_results:
        print("\n⚠️ 带宽测速无结果，使用 TCP 排序。")
        if USE_GLOBAL_MODE:
            final_selected = [node for node, _, _, _ in results[:GLOBAL_TOP_N]]
        else:
            final_selected = []
            for country, nodes_list in country_nodes.items():
                for node_str, _, _ in sorted(nodes_list, key=lambda x: (-x[2], x[1]))[:PER_COUNTRY_TOP_N]:
                    final_selected.append(node_str)
    else:
        speed_map = {node: speed for node, speed in bw_results}
        if USE_GLOBAL_MODE:
            final_selected = [node for node, _ in bw_results[:GLOBAL_TOP_N]]
        else:
            country_speed = defaultdict(list)
            for node, speed in bw_results:
                country = node.split('#')[-1] if '#' in node else ''
                if country:
                    country_speed[country].append((node, speed))
            final_selected = []
            for country, ns in country_speed.items():
                for node, _ in ns[:PER_COUNTRY_TOP_N]:
                    final_selected.append(node)
            final_selected.sort(key=lambda x: speed_map.get(x, 0), reverse=True)

        print("\n================ 最终优选节点 ================")
        for i, node in enumerate(final_selected, 1):
            speed = speed_map.get(node, 0)
            lat_sec = latency_map.get(node, float('inf'))
            if lat_sec != float('inf'):
                print(f"{i}. {node} {speed:.2f} Mbps {lat_sec*1000:.2f} ms")
            else:
                print(f"{i}. {node} {speed:.2f} Mbps")

    # ChatGPT 检测
    chatgpt_set = check_chatgpt_batch(final_selected)
    if chatgpt_set:
        print("\n================ ChatGPT 支持 ================")
        for node in final_selected:
            tag = " [ChatGPT]" if node in chatgpt_set else ""
            print(f"  {node}{tag}")

    # 写入结果文件
    write_ip_txt(final_selected, OUTPUT_FILE, speed_map=speed_map, latency_map=latency_map, chatgpt_set=chatgpt_set)
    print(f"\n结果已保存到 {OUTPUT_FILE}（{len(final_selected)} 个节点）")

    # 释放内存
    results = None
    candidates = None
    candidates_after = None
    gc.collect()

    # DNS 更新
    ip_list = [node.split(':')[0] for node in final_selected]
    batch_update_cloudflare_dns(ip_list, ip_info=avail_ip_info, full_bw_results=bw_results, latency_map=latency_map)

    # ===== Phase 3: 统一推送 GitHub =====
    print("\n" + "=" * 60)
    print("🚀 Phase 3: 推送结果到 GitHub")
    print("=" * 60)
    sync_to_github()
    print("\n✨ 全流程完成!")


# ==================== 入口 ====================
if __name__ == "__main__":
    import atexit
    import signal

    if ENABLE_LOGGING:
        try:
            script_dir = os.path.dirname(os.path.abspath(__file__))
            log_path = os.path.join(script_dir, LOG_FILE)
            log_f = open(log_path, "w", encoding="utf-8")
        except OSError as e:
            print(f"❌ 无法打开日志文件: {e}")
            log_f = None
        else:
            class _Tee:
                def __init__(self, terminal, log_file):
                    self.terminal = terminal
                    self.log_file = log_file
                def write(self, obj):
                    try:
                        self.terminal.write(obj)
                        self.terminal.flush()
                    except (OSError, ValueError):
                        pass
                    if obj and "\r" in obj and "\n" not in obj:
                        return
                    try:
                        self.log_file.write(obj)
                        self.log_file.flush()
                    except (OSError, ValueError):
                        pass
                def flush(self):
                    for f in (self.terminal, self.log_file):
                        try:
                            f.flush()
                        except (OSError, ValueError):
                            pass

            sys.stdout = _Tee(sys.stdout, log_f)

            def _close_log():
                try:
                    sys.stdout = sys.__stdout__
                    log_f.close()
                except (OSError, ValueError):
                    pass
            atexit.register(_close_log)

    def _handle_term_signal(signum, frame):
        print(f"\n⚠️ 收到信号 {signum}，正在退出...")
        sys.exit(128 + signum)

    if hasattr(signal, "SIGTERM"):
        try:
            signal.signal(signal.SIGTERM, _handle_term_signal)
        except (ValueError, OSError):
            pass
    if hasattr(signal, "SIGHUP") and sys.platform != "win32":
        try:
            signal.signal(signal.SIGHUP, _handle_term_signal)
        except (ValueError, OSError):
            pass

    try:
        main()
    except KeyboardInterrupt:
        print("\n⚠️ 用户中断 (Ctrl+C)")
        sys.exit(130)
