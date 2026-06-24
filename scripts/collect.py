from __future__ import annotations

import hashlib
import json
import re
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import date, datetime, timedelta, timezone
from pathlib import Path
from typing import Any
from html import unescape
from urllib.parse import quote, urlencode, urljoin

import feedparser
import requests
from dateutil import parser as dateparser
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"
DATA.mkdir(parents=True, exist_ok=True)

ARCHIVE_PATH = DATA / "archive.json"
LATEST_PATH = DATA / "latest.json"
KEYWORDS_PATH = DATA / "keywords.json"
ISSUES_PATH = DATA / "issues.json"
STATE_PATH = DATA / "state.json"

KST = timezone(timedelta(hours=9))
NOW = datetime.now(KST)
TODAY = NOW.date()
KEEP_START = TODAY - timedelta(days=400)
YEAR_START = TODAY - timedelta(days=364)

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 Chrome/149 Safari/537.36"
    )
}

# 공개된 공식 누리집 안의 자료만 검색하도록 도메인을 고정합니다.
OFFICIAL_POLICY_QUERIES = [
    (
        "국토교통부",
        "site:molit.go.kr/USR/NEWS/m_71/dtl.jsp "
        "(도시 OR 국토 OR 주택 OR 건축 OR 토지 OR 교통 OR 철도 OR 지역)",
    ),
    (
        "서울특별시",
        "site:seoul.go.kr/news/news_report.do "
        "(도시 OR 주택 OR 건축 OR 토지 OR 교통 OR 환경 OR 상권 OR 안전)",
    ),
    (
        "경기도",
        "site:gnews.gg.go.kr/briefing/brief_gongbo_view.do "
        "(도시 OR 주택 OR 건축 OR 토지 OR 교통 OR 환경 OR 산업단지 OR 지역)",
    ),
]


# 서울·인천 및 경기 주요 도시의 공식 고시공고 목록
MUNICIPAL_NOTICE_SOURCES = [
    {
        "city": "서울",
        "url": "https://www.seoul.go.kr/news/news_notice.do",
        "domain": "seoul.go.kr/news/news_notice.do",
    },
    {
        "city": "인천",
        "url": (
            "https://announce.incheon.go.kr/citynet/jsp/sap/"
            "SAPGosiBizProcess.do?command=searchList&flag=gosiGL&sido=ic&svp=Y"
        ),
        "domain": "announce.incheon.go.kr",
    },
    {
        "city": "수원",
        "url": (
            "https://www.suwon.go.kr/web/saeallOfr/BD_ofrList.do"
            "?q_currPage=1&q_rowPerPage=50"
        ),
        "domain": "suwon.go.kr/web/saeallOfr",
    },
    {
        "city": "화성",
        "url": (
            "https://www.hscity.go.kr/www/gosi/BD_notice.do"
            "?q_currPage=1&q_rowPerPage=50"
        ),
        "domain": "hscity.go.kr/www/gosi",
    },
    {
        "city": "남양주",
        "url": (
            "https://www.nyj.go.kr/www/selectEminwonWebList.do"
            "?cpn=1&key=2492&sa1Join=01%3B02%3B04%3B05"
        ),
        "domain": "nyj.go.kr/www/selectEminwonWeb",
    },
    {
        "city": "고양",
        "url": (
            "https://eminwon.goyang.go.kr/emwp/gov/mogaha/ntis/web/ofr/action/"
            "OfrAction.do?context=NTIS&countYn=Y&epcCheck=Y&homepage_pbs_yn=Y"
            "&initValue=Y&jndinm=OfrNotAncmtEJB&method=selectListOfrNotAncmt"
            "&methodnm=selectListOfrNotAncmtHomepage"
            "&not_ancmt_se_code=01%2C04%2C05&ofr_pageSize=50&subCheck=Y"
            "&title=%EA%B3%A0%EC%8B%9C%EA%B3%B5%EA%B3%A0"
        ),
        "domain": "eminwon.goyang.go.kr",
    },
    {
        "city": "성남",
        "url": (
            "https://www.seongnam.go.kr/notice/publicNotice01.do"
            "?menuIdx=1000055&returnURL=%2Fmain.do"
        ),
        "domain": "seongnam.go.kr/notice",
    },
    {
        "city": "평택",
        "url": (
            "https://www.pyeongtaek.go.kr/pyeongtaek/saeol/gosi/list.do"
            "?mid=0401020100"
        ),
        "domain": "pyeongtaek.go.kr/pyeongtaek/saeol/gosi",
    },
    {
        "city": "과천",
        "url": (
            "https://www.gccity.go.kr/portal/saeol/gosi/list.do"
            "?mId=0301040000"
        ),
        "domain": "gccity.go.kr/portal/saeol/gosi",
    },
    {
        "city": "광명",
        "url": (
            "https://www.gm.go.kr/pt/user/nftcBbs/BD_selectNftcBbsList.do"
            "?q_nftcBbsCode=1001"
        ),
        "domain": "gm.go.kr/pt/user/nftcBbs",
    },
    {
        "city": "광주",
        "url": (
            "https://www.gjcity.go.kr/portal/saeol/gosi/list.do"
            "?mId=0202010000"
        ),
        "domain": "gjcity.go.kr/portal/saeol/gosi",
    },
]

URBAN_NOTICE_KEYWORDS = (
    "도시관리계획",
    "도시계획시설",
    "도시기본계획",
    "지구단위계획",
    "정비구역",
    "정비계획",
    "정비사업",
    "재개발",
    "재건축",
    "소규모재건축",
    "가로주택정비",
    "재정비촉진",
    "도시개발",
    "개발계획",
    "산업단지계획",
    "주거환경개선",
    "공공주택",
    "역세권",
    "용도지역",
    "용도지구",
    "용도구역",
    "개발행위허가제한",
    "경관계획",
    "공원조성계획",
    "택지개발",
)

MUNICIPAL_NOTICE_DAYS = 7
MUNICIPAL_NOTICE_LIMIT = 28
MUNICIPAL_CITY_LIMIT = 4

# 단순 지형도면 고시와 실시계획 고시는 이번 목록에서 제외합니다.
MUNICIPAL_NOTICE_EXCLUDE_WORDS = (
    "지형도면",
    "실시계획",
)

EUM_GOSI_LIST_URL = "https://www.eum.go.kr/web/gs/gv/gvGosiList.jsp"


PUBLIC_MAINTENANCE_SOURCES = [
    {
        "city": "서울",
        "query": (
            "(site:seoul.go.kr OR site:cleanup.seoul.go.kr) "
            "(신속통합기획 OR 신통기획 OR 공공재개발 OR 공공재건축 "
            "OR 모아타운 OR 모아주택 OR 도심복합 OR 공공정비)"
        ),
    },
    {
        "city": "인천",
        "query": (
            "(site:incheon.go.kr OR site:ih.co.kr) "
            "(공공재개발 OR 공공재건축 OR 공공정비 OR 도심복합 "
            "OR 소규모주택정비 OR 정비사업지원)"
        ),
    },
    {
        "city": "수원",
        "query": (
            "site:suwon.go.kr "
            "(공공재개발 OR 공공재건축 OR 공공정비 OR 정비사업지원 "
            "OR 재개발재건축지원 OR 정비사업컨설팅)"
        ),
    },
    {
        "city": "화성",
        "query": (
            "site:hscity.go.kr "
            "(공공정비 OR 정비사업지원 OR 재개발재건축지원 "
            "OR 정비사업컨설팅 OR 소규모주택정비)"
        ),
    },
    {
        "city": "남양주",
        "query": (
            "site:nyj.go.kr "
            "(공공정비 OR 정비사업지원 OR 재개발재건축지원 "
            "OR 정비사업컨설팅 OR 소규모주택정비)"
        ),
    },
    {
        "city": "고양",
        "query": (
            "site:goyang.go.kr "
            "(공공정비 OR 정비사업지원 OR 재개발재건축지원 "
            "OR 정비사업컨설팅 OR 소규모주택정비)"
        ),
    },
    {
        "city": "성남",
        "query": (
            "site:seongnam.go.kr "
            "(공공재개발 OR 공공정비 OR 정비사업지원 "
            "OR 재개발재건축지원 OR 정비사업컨설팅)"
        ),
    },
    {
        "city": "평택",
        "query": (
            "site:pyeongtaek.go.kr "
            "(공공정비 OR 정비사업지원 OR 재개발재건축지원 "
            "OR 정비사업컨설팅 OR 소규모주택정비)"
        ),
    },
    {
        "city": "과천",
        "query": (
            "site:gccity.go.kr "
            "(공공정비 OR 정비사업지원 OR 재개발재건축지원 "
            "OR 정비사업컨설팅 OR 소규모주택정비)"
        ),
    },
    {
        "city": "광명",
        "query": (
            "site:gm.go.kr "
            "(공공재개발 OR 공공정비 OR 정비사업지원 "
            "OR 재개발재건축지원 OR 정비사업컨설팅)"
        ),
    },
    {
        "city": "광주",
        "query": (
            "site:gjcity.go.kr "
            "(공공정비 OR 정비사업지원 OR 재개발재건축지원 "
            "OR 정비사업컨설팅 OR 소규모주택정비)"
        ),
    },
]

PUBLIC_MAINTENANCE_KEYWORDS = (
    "신속통합기획",
    "신통기획",
    "공공재개발",
    "공공재건축",
    "공공정비",
    "공공참여",
    "공공지원",
    "모아타운",
    "모아주택",
    "도심복합",
    "정비사업 지원",
    "정비사업지원",
    "재개발·재건축 지원",
    "재개발재건축지원",
    "정비사업 컨설팅",
    "정비사업컨설팅",
    "정비사업 지원센터",
    "정비사업지원센터",
    "소규모주택정비",
)

PUBLIC_MAINTENANCE_DAYS = 7
PUBLIC_MAINTENANCE_LIMIT = 18
PUBLIC_MAINTENANCE_CITY_LIMIT = 3

OTHER_QUERIES = [
    (
        "법령",
        "법령·입법",
        "(site:opinion.lawmaking.go.kr OR site:law.go.kr) "
        "(도시 OR 국토 OR 주택 OR 주거 OR 건축 OR 토지 OR 정비 "
        "OR 재개발 OR 재건축 OR 공공주택 OR 교통 OR 철도 "
        "OR 도시개발 OR 도시재생 OR 공간 OR 지역 OR 농촌) "
        "(개정 OR 제정 OR 입법예고 OR 시행령 OR 시행규칙 OR 법률)",
    ),
    (
        "연구",
        "연구기관",
        "(site:krihs.re.kr OR site:si.re.kr OR site:auri.re.kr) "
        "(도시 OR 국토 OR 주택 OR 건축 OR 토지 OR 지역 OR 교통)",
    ),
    (
        "기사",
        "언론",
        "(도시계획 OR 국토계획 OR 지구단위계획 OR 용도지역 "
        "OR 도시개발 OR 도시재생 OR 재개발 OR 재건축 OR 지역소멸 "
        "OR 균형발전 OR 공공주택 OR 철도지하화 OR 스마트시티)",
    ),
]

RELEVANT_WORDS = (
    "도시", "국토", "주택", "건축", "부동산", "토지", "교통", "철도",
    "도로", "지역", "재생", "정비", "개발", "계획", "공간", "생활권",
    "상권", "빈집", "인구", "소멸", "균형발전", "스마트시티",
    "스마트도시", "산업단지", "공공주택", "재개발", "재건축", "경관",
    "농촌", "기반시설", "광역", "역세권", "기후", "탄소중립",
    "녹색건축", "용도지역", "지구단위", "공공건축", "도심", "택지",
    "국가산단", "상업지역", "GTX", "생활인구", "도심융합",
    "노후계획도시", "철도지하화", "산업전환", "도시혁신", "주거복지",
    "공실", "침수", "폭염",
)

STOPWORDS = {
    "연구", "방안", "위한", "관련", "대한", "통한", "기반", "추진",
    "발표", "개최", "결과", "입법예고", "보도자료", "보고서", "서울시",
    "경기도", "국토교통부", "국토연구원", "서울연구원", "건축공간연구원",
    "정책", "계획", "마련", "강화", "지원", "개선", "확대", "제도",
    "사업", "대응", "활성화", "종합", "새로운", "최근", "전국", "정부",
    "분석", "방향", "현황", "통해", "관한", "기자", "뉴스", "지역",
    "도시", "국토", "올해", "내년", "한국", "대상",
}

TOPICS = {
    "주택공급·공공주택": (
        "주택공급", "공공주택", "택지", "임대주택", "주거복지", "분양"
    ),
    "재건축·재개발·정비사업": (
        "재건축", "재개발", "정비사업", "노후계획도시", "1기 신도시"
    ),
    "지역소멸·균형발전": (
        "지역소멸", "지방소멸", "균형발전", "생활인구", "인구감소"
    ),
    "철도·광역교통·역세권": (
        "철도", "GTX", "광역교통", "역세권", "철도지하화", "도시철도"
    ),
    "도시재생·빈집·원도심": (
        "도시재생", "빈집", "원도심", "구도심", "유휴공간", "공실"
    ),
    "국토계획·용도지역·규제": (
        "국토계획", "도시계획", "용도지역", "지구단위계획",
        "개발제한구역", "그린벨트", "용적률"
    ),
    "산업단지·지역산업 전환": (
        "산업단지", "국가산단", "산업전환", "기업도시", "첨단산업"
    ),
    "스마트시티·AI·디지털전환": (
        "스마트시티", "스마트도시", "인공지능", "디지털트윈",
        "자율주행", "도시데이터"
    ),
    "기후위기·탄소중립·녹색건축": (
        "기후위기", "탄소중립", "녹색건축", "제로에너지",
        "침수", "폭염", "기후적응"
    ),
    "상권·골목경제·생활권": (
        "상권", "골목상권", "생활권", "전통시장", "공실",
        "젠트리피케이션"
    ),
    "농촌공간·농촌재생": (
        "농촌공간", "농촌재생", "농촌마을", "농촌소멸", "농촌협약"
    ),
    "건축정책·공공건축": (
        "건축정책", "공공건축", "건축물관리", "노후건축물", "건축안전"
    ),
    "토지·부동산시장": (
        "부동산", "토지거래", "집값", "지가", "공시가격", "전세",
        "매매가격"
    ),
    "관광·지역개발": (
        "관광단지", "지역개발", "관광개발", "문화도시", "복합개발",
        "워케이션"
    ),
    "도시안전·재난 대응": (
        "도시안전", "재난", "지진", "산사태", "침수", "화재",
        "안전진단", "붕괴"
    ),
}

TOKEN_RE = re.compile(r"[가-힣]{2,}")

# 기관명·언론사명이 아니라 실제 도시계획 이슈가 집계되도록
# 의미 있는 도시·건축·국토 분야 용어를 우선 집계합니다.
KEYWORD_PHRASES = {
    "재건축": ("재건축",),
    "재개발": ("재개발",),
    "정비사업": ("정비사업", "도시정비"),
    "노후계획도시": ("노후계획도시", "1기 신도시"),
    "주택공급": ("주택공급", "주택 공급"),
    "공공주택": ("공공주택", "공공임대"),
    "임대주택": ("임대주택",),
    "주거복지": ("주거복지",),
    "도시재생": ("도시재생",),
    "빈집": ("빈집",),
    "원도심": ("원도심", "구도심"),
    "지역소멸": ("지역소멸", "지방소멸"),
    "균형발전": ("균형발전",),
    "생활인구": ("생활인구",),
    "인구감소지역": ("인구감소지역",),
    "도시계획": ("도시계획",),
    "국토계획": ("국토계획",),
    "토지이용": ("토지이용",),
    "지구단위계획": ("지구단위계획",),
    "용도지역": ("용도지역",),
    "개발제한구역": ("개발제한구역", "그린벨트"),
    "용적률": ("용적률",),
    "공공기여": ("공공기여",),
    "도시개발": ("도시개발",),
    "역세권": ("역세권",),
    "광역교통": ("광역교통",),
    "GTX": ("gtx",),
    "철도지하화": ("철도지하화",),
    "도시철도": ("도시철도",),
    "산업단지": ("산업단지", "국가산단"),
    "도시공업지역": ("도시공업지역",),
    "도심융합특구": ("도심융합특구",),
    "기회발전특구": ("기회발전특구",),
    "스마트시티": ("스마트시티", "스마트도시"),
    "디지털트윈": ("디지털트윈",),
    "공공건축": ("공공건축",),
    "건축물관리": ("건축물관리", "노후건축물"),
    "녹색건축": ("녹색건축", "제로에너지"),
    "탄소중립": ("탄소중립",),
    "기후위기": ("기후위기", "기후적응"),
    "침수": ("침수",),
    "폭염": ("폭염",),
    "골목상권": ("골목상권",),
    "전통시장": ("전통시장",),
    "농촌공간": ("농촌공간",),
    "농촌재생": ("농촌재생",),
    "토지거래": ("토지거래",),
    "부동산시장": ("부동산시장", "주택시장"),
    "공시가격": ("공시가격",),
    "관광단지": ("관광단지",),
    "복합개발": ("복합개발",),
    "경관": ("경관",),
    "문화재": ("문화재", "국가유산"),
    "기반시설": ("기반시설",),
}

# 의미가 약한 행정용어와 기관·언론사·사이트 명칭은 후보에서 제외합니다.
KEYWORD_NOISE = STOPWORDS | {
    "국가법령정보센터", "국민참여입법센터", "한국주택경제신문",
    "서울연구데이터서비스", "하우징헤럴드", "경기도뉴스포털",
    "연합뉴스", "서울특별시", "서울특별시청", "대한민국정책브리핑",
    "정책브리핑", "머니투데이", "매일경제", "한국경제", "조선일보",
    "중앙일보", "동아일보", "한겨레", "경향신문", "뉴스1", "뉴시스",
    "조례", "자치법규", "행정규칙", "구역", "선정", "지정", "고시",
    "공고", "일부개정", "전부개정", "개정안", "폐지", "시행",
    "입법", "예고", "의견", "제출", "알림", "모집", "공모", "접수",
    "보도", "자료", "센터", "포털", "서비스", "신문", "헤럴드",
}


# 자료 품질 필터
# 1) 연구기관의 단순 사진·행사 스케치 게시물은 제외
# 2) 법령명이 없이 '변경 조문' 등만 표시된 자료는 제외
RESEARCH_MEDIA_PATTERNS = (
    # 단순 사진·옛 모습 공유
    r"^\s*\[(?:포토|사진|photo)\]",
    r"^\s*(?:포토\s*뉴스|포토\s*갤러리|포토\s*앨범)\b",
    r"사진으로\s*보는",
    r"(?:옛|과거|예전)\s*(?:사진|모습|풍경)",
    r"(?:사진|기록)\s*아카이브",
    r"(?:기록|역사)\s*사진",
    r"그때\s*그\s*시절",
    r"추억(?:의)?\s*(?:사진|거리|풍경|모습)",
    r"(?:옛|과거|예전).{0,20}(?:길|거리|로|동네|마을).{0,20}(?:사진|모습|풍경)",
    r"(?:길|거리|로|동네|마을).{0,20}(?:옛|과거|예전).{0,20}(?:사진|모습|풍경)",
    r"(?:현장|행사|세미나|포럼)\s*스케치",
    r"(?:행사|현장)\s*사진",
    r"사진\s*(?:공유|모음|자료|갤러리|앨범)",

    # 연구성과가 아닌 기관 홍보·행정 게시물
    r"(?:채용|직원|연구원)\s*(?:공고|모집)",
    r"(?:입찰|용역|계약)\s*(?:공고|안내)",
    r"(?:참가자|교육생|수강생|서포터즈|기자단)\s*모집",
    r"(?:행사|세미나|포럼|설명회|교육)\s*(?:개최\s*)?안내",
    r"(?:참가|수강)\s*(?:신청|접수)",
    r"(?:업무협약|협약식|mou|개소식|방문단|기관방문)",
    r"(?:카드뉴스|홍보영상|기관동정|수상소식|뉴스레터)",
)


LAW_GENERIC_PHRASES = (
    "변경 조문",
    "변경조문",
    "신구 조문 대비표",
    "신구조문대비표",
    "개정문",
    "제정·개정 이유",
    "제정개정이유",
    "조문 정보",
    "조문정보",
    "법령 체계도",
    "법령체계도",
)

LAW_NAME_SIGNALS = (
    "법률", "특별법", "기본법", "시행령", "시행규칙",
    "조례", "규정", "기준", "지침",
)


# 법령 제목 자체에 아래 도시계획 관련 키워드가 있어야 공유합니다.
LAW_RELEVANT_KEYWORDS = (
    "도시", "국토", "주택", "주거", "건축", "토지", "부동산",
    "정비", "재개발", "재건축", "공공주택", "도시개발",
    "도시재생", "빈집", "교통", "철도", "도로", "주차",
    "공간", "지역", "농촌", "산업단지", "물류", "경관",
    "공원", "녹지", "기반시설", "용도지역", "지구단위",
    "택지", "역세권", "생활권", "기후", "탄소", "환경",
)

LAW_GENERIC_TITLE_PATTERNS = (
    r"^\s*(?:관련\s*)?법령\s*$",
    r"^\s*(?:관련\s*)?법령\s*(?:개정|제정|변경|안내)\s*$",
    r"^\s*(?:법률|시행령|시행규칙)\s*(?:개정|제정|변경)\s*$",
    r"^\s*(?:일부|전부)?개정(?:안|령안)?\s*$",
    r"^\s*(?:명칭|제명)\s*(?:변경|개칭)\s*$",
)

LAW_RENAME_PATTERNS = (
    r"(?:법령|법률|조례|규정).{0,12}(?:명칭|제명).{0,8}(?:변경|개칭)",
    r"(?:명칭|제명).{0,8}(?:변경|개칭)",
)

FILTER_COUNTS: Counter[str] = Counter()


# 무료 자동 이슈 분석 규칙 V2
# 고정된 '핵심 변화/주요 쟁점/도시계획적 영향' 문장을 강제로 만들지 않습니다.
# 관련 자료 10~15건의 제목에서 실제로 2건 이상 반복된 흐름만 표시합니다.
FLOW_DIMENSIONS = {
    "정책·제도": {
        "개정": "법령 개정",
        "시행": "제도 시행",
        "완화": "규제 완화",
        "강화": "관리 강화",
        "도입": "새 제도 도입",
        "지정": "구역·사업 지정",
        "지원": "지원 확대",
        "공모": "사업 공모",
        "승인": "계획·사업 승인",
    },
    "사업·공급": {
        "추진": "사업 추진",
        "공급": "공급 확대",
        "착공": "사업 착공",
        "준공": "사업 준공",
        "조성": "공간·시설 조성",
        "정비": "정비 추진",
        "유치": "기능·기업 유치",
        "계획": "계획 수립",
    },
    "시장·비용": {
        "사업성": "사업성",
        "공사비": "공사비",
        "분담금": "분담금",
        "미분양": "미분양",
        "가격": "가격 변동",
        "거래": "거래 변화",
        "지가": "지가 변화",
        "임대료": "임대료",
        "부담": "비용 부담",
    },
    "갈등·리스크": {
        "갈등": "이해관계자 갈등",
        "반발": "주민 반발",
        "반대": "반대 여론",
        "소송": "법적 분쟁",
        "지연": "사업 지연",
        "취소": "사업 취소",
        "무산": "사업 무산",
        "논란": "정책·사업 논란",
    },
    "공간·생활권": {
        "역세권": "역세권 재편",
        "상권": "상권 변화",
        "생활권": "생활권 변화",
        "빈집": "빈집 관리",
        "인구": "인구 변화",
        "소멸": "지역소멸",
        "교통": "교통체계 변화",
        "철도": "철도축 변화",
        "용적률": "개발밀도 변화",
        "산업단지": "산업입지 변화",
    },
    "안전·환경": {
        "침수": "침수 대응",
        "폭염": "폭염 대응",
        "기후": "기후위기 대응",
        "탄소": "탄소중립",
        "안전": "안전관리",
        "재난": "재난 대응",
        "녹색": "녹색건축",
    },
}

FLOW_SENTENCE = {
    "정책·제도": "{labels} 관련 움직임이 {titles}건의 자료에서 반복됐다.",
    "사업·공급": "{labels} 흐름이 {titles}건의 자료에서 확인됐다.",
    "시장·비용": "{labels} 문제가 {titles}건의 자료에서 주요 관심사로 나타났다.",
    "갈등·리스크": "{labels} 위험이 {titles}건의 자료에서 반복적으로 제기됐다.",
    "공간·생활권": "{labels}가 {titles}건의 자료에서 공간 변화의 핵심으로 나타났다.",
    "안전·환경": "{labels}이 {titles}건의 자료에서 주요 대응 과제로 나타났다.",
}


def diversify_issue_rows(
    matched: list[dict[str, str]],
    limit: int = 15,
) -> list[dict[str, str]]:
    """같은 출처가 분석을 독점하지 않도록 출처별 최대 2건을 우선 반영합니다."""
    selected: list[dict[str, str]] = []
    source_counts: Counter[str] = Counter()
    seen_titles: set[str] = set()

    for row in matched:
        source = clean(row.get("source", "")) or "출처 미상"
        key = title_key(row.get("title", ""))
        if not key or key in seen_titles:
            continue
        if source_counts[source] >= 2:
            continue

        selected.append(row)
        seen_titles.add(key)
        source_counts[source] += 1

        if len(selected) >= limit:
            break

    if len(selected) < min(10, len(matched)):
        for row in matched:
            key = title_key(row.get("title", ""))
            if not key or key in seen_titles:
                continue
            selected.append(row)
            seen_titles.add(key)
            if len(selected) >= limit:
                break

    return selected


def build_issue_summary(
    topic: str,
    basis_rows: list[dict[str, str]],
) -> dict[str, Any]:
    titles = [
        strip_source_suffix(row.get("title", ""), row.get("source", ""))
        for row in basis_rows
        if row.get("title")
    ]

    points: list[dict[str, Any]] = []

    for dimension, signals in FLOW_DIMENSIONS.items():
        label_counts: Counter[str] = Counter()
        matched_title_count = 0

        for title in titles:
            lower = title.lower()
            labels_in_title: set[str] = set()

            for signal, label in signals.items():
                if signal.lower() in lower:
                    labels_in_title.add(label)

            if labels_in_title:
                matched_title_count += 1
                label_counts.update(labels_in_title)

        # 한 기사에서만 나온 말은 '흐름'으로 보지 않습니다.
        if matched_title_count < 2:
            continue

        top_labels = [
            label for label, _ in label_counts.most_common(3)
        ]
        if not top_labels:
            continue

        labels_text = "·".join(top_labels)
        sentence = FLOW_SENTENCE[dimension].format(
            labels=labels_text,
            titles=matched_title_count,
        )

        points.append(
            {
                "label": dimension,
                "text": sentence,
                "evidence_count": matched_title_count,
            }
        )

    points.sort(
        key=lambda point: point["evidence_count"],
        reverse=True,
    )

    # 최대 3개 흐름만 표시합니다.
    points = points[:3]

    if not points:
        note = (
            "관련 제목들 사이에서 2건 이상 반복된 공통 흐름이 뚜렷하지 않아 "
            "대표 자료만 제시합니다."
        )
    else:
        note = ""

    return {
        "points": points,
        "note": note,
        "topic": topic,
    }


def exclusion_reason(category: str, title: str) -> str | None:
    value = clean(title)
    lower = value.lower()

    if category == "연구":
        for pattern in RESEARCH_MEDIA_PATTERNS:
            if re.search(pattern, lower, flags=re.I):
                return "연구 사진·홍보·행정 게시물"

    if category == "법령":
        normalized = re.sub(r"[^0-9a-z가-힣]+", "", lower)

        # 도시계획 관련 키워드가 제목에 없는 법령은 공유하지 않습니다.
        if not any(
            keyword.lower() in lower
            for keyword in LAW_RELEVANT_KEYWORDS
        ):
            return "도시계획 관련 키워드 없는 법령"

        # '관련 법령 개정', '명칭 변경', '개칭' 같은 일반 제목 제외
        for pattern in LAW_GENERIC_TITLE_PATTERNS:
            if re.fullmatch(pattern, lower, flags=re.I):
                return "일반적인 법령 개정 제목"

        for pattern in LAW_RENAME_PATTERNS:
            if re.search(pattern, lower, flags=re.I):
                return "단순 명칭 변경 법령"

        # 법령명이 전혀 없이 일반 메뉴명만 제목으로 잡힌 경우
        if re.fullmatch(
            r"(변경조문|신구조문대비표|개정문|제정개정이유|"
            r"조문정보|법령체계도)(?:시행\d+)?",
            normalized,
        ):
            return "법령명 없는 일반 조문 페이지"

        if re.fullmatch(
            r"(별표|별지|서식)(?:제?\d+(?:의\d+)?)?(?:시행\d+)?",
            normalized,
        ):
            return "법령명 없는 별표·별지 페이지"

        has_generic_phrase = any(
            phrase.lower() in lower
            for phrase in LAW_GENERIC_PHRASES
        )
        has_law_name = any(
            signal.lower() in lower
            for signal in LAW_NAME_SIGNALS
        )
        if has_generic_phrase and not has_law_name:
            return "법령명 없는 일반 조문 페이지"

    return None


def make_session() -> requests.Session:
    session = requests.Session()
    retry = Retry(
        total=3,
        connect=3,
        read=3,
        backoff_factor=0.8,
        status_forcelist=(429, 500, 502, 503, 504),
        allowed_methods=("GET",),
    )
    adapter = HTTPAdapter(max_retries=retry)
    session.mount("https://", adapter)
    session.mount("http://", adapter)
    session.headers.update(HEADERS)
    return session


HTTP = make_session()


def clean(value: Any) -> str:
    return re.sub(r"\s+", " ", str(value or "")).strip()


def strip_source_suffix(title: str, source: str = "") -> str:
    """Google 뉴스 제목 뒤의 '- 언론사/기관명' 꼬리표를 제거합니다."""
    value = clean(title)

    if source:
        for separator in (" - ", " – ", " — ", " | "):
            suffix = separator + clean(source)
            if value.lower().endswith(suffix.lower()):
                value = value[:-len(suffix)].strip()
                break

    # 기존 archive에는 실제 언론사명이 source 필드에 없는 항목도 있으므로
    # 제목 맨 끝의 짧은 출처 꼬리표를 한 번 더 제거합니다.
    value = re.sub(
        r"\s+(?:-|–|—|\|)\s+[^|–—-]{2,50}$",
        "",
        value,
    ).strip()
    return value


def load_json(path: Path, default: Any) -> Any:
    if not path.exists():
        return default
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except Exception:
        return default


def parse_date(value: Any) -> date | None:
    if not value:
        return None
    try:
        parsed = dateparser.parse(str(value))
        return parsed.date() if parsed else None
    except Exception:
        return None


def entry_date(entry: Any) -> date | None:
    for key in ("published", "updated", "dc_date"):
        parsed = parse_date(entry.get(key))
        if parsed:
            return parsed
    for key in ("published_parsed", "updated_parsed"):
        value = entry.get(key)
        if value:
            try:
                return date(value.tm_year, value.tm_mon, value.tm_mday)
            except Exception:
                pass
    return None


def title_key(title: str) -> str:
    value = clean(title).lower()
    value = re.sub(r"\s*[-–—]\s*[^-–—]{2,40}$", "", value)
    return re.sub(r"[^0-9a-z가-힣]+", "", value)


def is_relevant(title: str) -> bool:
    lower = title.lower()
    return any(word.lower() in lower for word in RELEVANT_WORDS)


def make_item(
    title: str,
    url: str,
    source: str,
    category: str,
    published: date | None,
) -> dict[str, str] | None:
    title = clean(title)
    url = clean(url)
    if len(title) < 5 or not url or not published:
        return None
    if published < KEEP_START or published > TODAY + timedelta(days=1):
        return None

    reason = exclusion_reason(category, title)
    if reason:
        FILTER_COUNTS[reason] += 1
        return None

    key = f"{published.isoformat()}|{title_key(title)}"
    return {
        "id": hashlib.sha1(key.encode("utf-8")).hexdigest()[:16],
        "title": title,
        "url": url,
        "source": source,
        "category": category,
        "date": published.isoformat(),
    }



def strip_html(value: str) -> str:
    value = re.sub(r"(?is)<script.*?</script>|<style.*?</style>", " ", value)
    value = re.sub(r"(?s)<[^>]+>", " ", value)
    return clean(unescape(value))


def parse_notice_date(value: str) -> date | None:
    match = re.search(
        r"(20\d{2})[./-]\s*(\d{1,2})[./-]\s*(\d{1,2})",
        value,
    )
    if not match:
        return None
    try:
        return date(
            int(match.group(1)),
            int(match.group(2)),
            int(match.group(3)),
        )
    except ValueError:
        return None


def is_urban_notice(title: str) -> bool:
    lower = clean(title).lower()

    if any(word.lower() in lower for word in MUNICIPAL_NOTICE_EXCLUDE_WORDS):
        return False

    return any(keyword.lower() in lower for keyword in URBAN_NOTICE_KEYWORDS)


def make_eum_gosi_url(title: str, published: date) -> str:
    # 토지이음 고시정보에서 제목과 날짜로 다시 확인할 수 있게 합니다.
    params = {
        "startdt": (published - timedelta(days=2)).isoformat(),
        "enddt": (published + timedelta(days=2)).isoformat(),
        "zonenm": clean(title),
        "pageNo": "1",
    }
    return EUM_GOSI_LIST_URL + "?" + urlencode(params)


def extract_notice_rows(
    html_text: str,
    source: dict[str, str],
) -> list[dict[str, str]]:
    cutoff = TODAY - timedelta(days=MUNICIPAL_NOTICE_DAYS - 1)
    blocks = re.findall(r"(?is)<tr\b[^>]*>.*?</tr>", html_text)
    blocks += re.findall(r"(?is)<li\b[^>]*>.*?</li>", html_text)

    rows: list[dict[str, str]] = []
    seen: set[str] = set()

    for block in blocks:
        block_text = strip_html(block)
        published = parse_notice_date(block_text)
        if not published or published < cutoff or published > TODAY + timedelta(days=1):
            continue

        anchors = re.findall(
            r"(?is)<a\b[^>]*href=[\"']([^\"']+)[\"'][^>]*>(.*?)</a>",
            block,
        )

        candidates: list[tuple[str, str]] = []
        for href, label_html in anchors:
            title = strip_html(label_html)
            if len(title) < 6 or not is_urban_notice(title):
                continue
            candidates.append((title, href))

        if not candidates:
            continue

        title, href = max(candidates, key=lambda item: len(item[0]))
        key = f"{source['city']}|{published.isoformat()}|{title_key(title)}"
        if key in seen:
            continue
        seen.add(key)

        eum_url = make_eum_gosi_url(title, published)

        if href.lower().startswith("javascript:") or href.startswith("#"):
            link = eum_url
            source_type = "토지이음 확인"
        else:
            link = urljoin(source["url"], href)
            source_type = "공식 고시공고"

        rows.append(
            {
                "city": source["city"],
                "title": title,
                "url": link,
                "eum_url": eum_url,
                "date": published.isoformat(),
                "source_type": source_type,
            }
        )

    return rows


def fallback_municipal_notices(
    source: dict[str, str],
) -> list[dict[str, str]]:
    terms = (
        "(도시관리계획 OR 도시계획시설 OR 지구단위계획 OR 정비구역 "
        "OR 재개발 OR 재건축 OR 도시개발 OR 정비계획 OR 용도지역)"
    )
    query = (
        f"site:{source['domain']} {terms} "
        f"when:{MUNICIPAL_NOTICE_DAYS}d"
    )
    url = (
        "https://news.google.com/rss/search?q="
        + quote(query)
        + "&hl=ko&gl=KR&ceid=KR:ko"
    )
    response = HTTP.get(url, timeout=(12, 35))
    response.raise_for_status()
    parsed = feedparser.parse(response.content)

    cutoff = TODAY - timedelta(days=MUNICIPAL_NOTICE_DAYS - 1)
    rows: list[dict[str, str]] = []
    seen: set[str] = set()

    for entry in parsed.entries[:60]:
        source_data = entry.get("source") or {}
        feed_source = (
            clean(source_data.get("title"))
            if isinstance(source_data, dict)
            else ""
        )
        title = strip_source_suffix(clean(entry.get("title")), feed_source)
        published = entry_date(entry)

        if (
            not published
            or published < cutoff
            or not is_urban_notice(title)
        ):
            continue

        key = f"{source['city']}|{published.isoformat()}|{title_key(title)}"
        if key in seen:
            continue
        seen.add(key)

        rows.append(
            {
                "city": source["city"],
                "title": title,
                "url": clean(entry.get("link", "")) or source["url"],
                "eum_url": make_eum_gosi_url(title, published),
                "date": published.isoformat(),
                "source_type": "공식 누리집 검색",
            }
        )

    return rows


def collect_one_municipal_source(
    source: dict[str, str],
) -> tuple[list[dict[str, str]], str]:
    direct_error = ""
    try:
        response = HTTP.get(
            source["url"],
            timeout=(12, 35),
            allow_redirects=True,
        )
        response.raise_for_status()
        response.encoding = response.apparent_encoding or response.encoding
        rows = extract_notice_rows(response.text, source)
        if rows:
            return rows, f"공식 목록 {len(rows)}건"
        direct_error = "공식 목록 0건"
    except Exception as exc:
        direct_error = f"공식 목록 {type(exc).__name__}"

    try:
        fallback = fallback_municipal_notices(source)
        if fallback:
            return fallback, f"{direct_error}, 검색보완 {len(fallback)}건"
        return [], f"{direct_error}, 검색보완 0건"
    except Exception as exc:
        return [], f"{direct_error}, 검색보완 {type(exc).__name__}"


def collect_municipal_notices(
) -> tuple[list[dict[str, str]], dict[str, str]]:
    all_rows: list[dict[str, str]] = []
    status: dict[str, str] = {}

    with ThreadPoolExecutor(max_workers=6) as executor:
        future_map = {
            executor.submit(collect_one_municipal_source, source): source
            for source in MUNICIPAL_NOTICE_SOURCES
        }

        for future in as_completed(future_map):
            source = future_map[future]
            try:
                rows, message = future.result()
                all_rows.extend(rows)
                status[source["city"]] = message
            except Exception as exc:
                status[source["city"]] = f"수집 실패: {type(exc).__name__}"

    deduped: dict[str, dict[str, str]] = {}
    for row in all_rows:
        key = f"{row['city']}|{row['date']}|{title_key(row['title'])}"
        deduped[key] = row

    sorted_rows = sorted(
        deduped.values(),
        key=lambda row: (row["date"], row["city"]),
        reverse=True,
    )

    selected: list[dict[str, str]] = []
    city_counts: Counter[str] = Counter()

    for row in sorted_rows:
        if city_counts[row["city"]] >= MUNICIPAL_CITY_LIMIT:
            continue
        selected.append(row)
        city_counts[row["city"]] += 1
        if len(selected) >= MUNICIPAL_NOTICE_LIMIT:
            break

    return selected, status


def google_news(
    query: str,
    category: str,
    source_hint: str,
) -> list[dict[str, str]]:
    url = (
        "https://news.google.com/rss/search?q="
        + quote(query)
        + "&hl=ko&gl=KR&ceid=KR:ko"
    )
    response = HTTP.get(url, timeout=(12, 35))
    response.raise_for_status()
    parsed = feedparser.parse(response.content)

    rows: list[dict[str, str]] = []
    for entry in parsed.entries[:100]:
        raw_title = clean(entry.get("title"))
        published = entry_date(entry)
        source_data = entry.get("source") or {}
        feed_source = (
            clean(source_data.get("title"))
            if isinstance(source_data, dict)
            else ""
        )

        title = strip_source_suffix(raw_title, feed_source)
        if category == "정책" and not is_relevant(title):
            continue

        if category == "정책" and source_hint in {
            "국토교통부", "서울특별시", "경기도"
        }:
            final_source = source_hint
        else:
            final_source = feed_source or source_hint or "Google 뉴스"

        row = make_item(
            title=title,
            url=entry.get("link", ""),
            source=final_source,
            category=category,
            published=published,
        )
        if row:
            rows.append(row)
    return rows



def collect_public_maintenance_updates(
) -> tuple[list[dict[str, str]], dict[str, str]]:
    rows: list[dict[str, str]] = []
    status: dict[str, str] = {}
    cutoff = TODAY - timedelta(days=PUBLIC_MAINTENANCE_DAYS - 1)

    def collect_one(source: dict[str, str]) -> tuple[str, list[dict[str, str]]]:
        city = source["city"]
        query = source["query"] + f" when:{PUBLIC_MAINTENANCE_DAYS}d"
        found = google_news(query, "정비", city)

        selected: list[dict[str, str]] = []
        for row in found:
            title = clean(row.get("title", ""))
            published = row_date(row)
            if not published or published < cutoff:
                continue
            if not any(
                keyword.lower() in title.lower()
                for keyword in PUBLIC_MAINTENANCE_KEYWORDS
            ):
                continue

            copied = dict(row)
            copied["city"] = city
            copied["source"] = city
            copied["source_type"] = "공식 정비사업 소식"
            selected.append(copied)

        return city, selected

    with ThreadPoolExecutor(max_workers=6) as executor:
        futures = {
            executor.submit(collect_one, source): source
            for source in PUBLIC_MAINTENANCE_SOURCES
        }
        for future in as_completed(futures):
            source = futures[future]
            city = source["city"]
            try:
                _, found = future.result()
                rows.extend(found)
                status[city] = f"{len(found)}건"
            except Exception as exc:
                status[city] = f"수집 실패: {type(exc).__name__}"

    unique: dict[str, dict[str, str]] = {}
    for row in rows:
        key = f"{row.get('city')}|{row.get('date')}|{title_key(row.get('title', ''))}"
        unique[key] = row

    ordered = sorted(
        unique.values(),
        key=lambda row: (row.get("date", ""), row.get("city", "")),
        reverse=True,
    )

    output: list[dict[str, str]] = []
    city_counts: Counter[str] = Counter()

    for row in ordered:
        city = row.get("city", "")
        if city_counts[city] >= PUBLIC_MAINTENANCE_CITY_LIMIT:
            continue
        output.append(row)
        city_counts[city] += 1
        if len(output) >= PUBLIC_MAINTENANCE_LIMIT:
            break

    return output, status

def month_windows() -> list[tuple[date, date]]:
    windows: list[tuple[date, date]] = []
    end = TODAY + timedelta(days=1)
    while end > YEAR_START:
        start = max(YEAR_START, end - timedelta(days=31))
        windows.append((start, end))
        end = start
    return windows


def current_jobs() -> list[tuple[str, str, str]]:
    jobs: list[tuple[str, str, str]] = []
    for source, query in OFFICIAL_POLICY_QUERIES:
        jobs.append(("정책", source, f"{query} when:14d"))
    for category, source, query in OTHER_QUERIES:
        jobs.append((category, source, f"{query} when:30d"))
    return jobs


def backfill_jobs() -> list[tuple[str, str, str]]:
    jobs: list[tuple[str, str, str]] = []
    for start, end in month_windows():
        suffix = f" after:{start.isoformat()} before:{end.isoformat()}"
        for source, query in OFFICIAL_POLICY_QUERIES:
            jobs.append(("정책", source, query + suffix))
        for category, source, query in OTHER_QUERIES:
            jobs.append((category, source, query + suffix))
    return jobs


def run_jobs(
    jobs: list[tuple[str, str, str]],
    label: str,
) -> tuple[list[dict[str, str]], dict[str, str]]:
    rows: list[dict[str, str]] = []
    status: dict[str, str] = {}
    source_counts: Counter[str] = Counter()
    failures: Counter[str] = Counter()

    with ThreadPoolExecutor(max_workers=6) as executor:
        future_map = {
            executor.submit(google_news, query, category, source):
            (category, source, query)
            for category, source, query in jobs
        }

        for future in as_completed(future_map):
            category, source, _ = future_map[future]
            try:
                found = future.result()
                rows.extend(found)
                source_counts[source] += len(found)
            except Exception as exc:
                failures[source] += 1
                print(f"[{label}] {source} 실패: {type(exc).__name__}: {exc}")

    for _, source, _ in jobs:
        if source in status:
            continue
        count = source_counts[source]
        failed = failures[source]
        if count:
            status[source] = f"{count}건 수집"
        elif failed:
            status[source] = f"수집 실패 {failed}회"
        else:
            status[source] = "검색 결과 0건"

    return rows, status


def deduplicate(rows: list[dict[str, str]]) -> list[dict[str, str]]:
    result: dict[str, dict[str, str]] = {}
    official = {"국토교통부", "서울특별시", "경기도"}

    for original in rows:
        row = dict(original)
        row["title"] = strip_source_suffix(
            row.get("title", ""),
            row.get("source", ""),
        )

        reason = exclusion_reason(
            row.get("category", ""),
            row.get("title", ""),
        )
        if reason:
            FILTER_COUNTS[reason] += 1
            continue

        key = f"{row.get('date', '')}|{title_key(row.get('title', ''))}"
        old = result.get(key)
        if old is None:
            result[key] = row
            continue

        if (
            row.get("source") in official
            and old.get("source") not in official
        ):
            result[key] = row

    return list(result.values())


def row_date(row: dict[str, str]) -> date | None:
    try:
        return date.fromisoformat(row["date"])
    except Exception:
        return None


def period_rows(
    rows: list[dict[str, str]],
    days: int,
) -> list[dict[str, str]]:
    cutoff = TODAY - timedelta(days=days - 1)
    return [
        row for row in rows
        if row_date(row) and row_date(row) >= cutoff
    ]


def category_counts(
    rows: list[dict[str, str]],
    days: int,
) -> dict[str, int]:
    counter = Counter(row["category"] for row in period_rows(rows, days))
    return {
        "정책": counter.get("정책", 0),
        "법령": counter.get("법령", 0),
        "연구": counter.get("연구", 0),
        "기사": counter.get("기사", 0),
    }


def keyword_text(row: dict[str, str]) -> str:
    title = strip_source_suffix(
        row.get("title", ""),
        row.get("source", ""),
    )
    text = title

    # URL 조각과 기관·언론사명을 제거합니다.
    text = re.sub(r"https?://\S+|www\.\S+", " ", text, flags=re.I)
    source = clean(row.get("source", ""))
    if source:
        text = re.sub(re.escape(source), " ", text, flags=re.I)

    for noise in KEYWORD_NOISE:
        if len(noise) >= 2:
            text = re.sub(re.escape(noise), " ", text, flags=re.I)

    return clean(text)


def keyword_rows(
    rows: list[dict[str, str]],
    days: int,
) -> list[dict[str, Any]]:
    phrase_counter: Counter[str] = Counter()
    fallback_counter: Counter[str] = Counter()

    for row in period_rows(rows, days):
        original = strip_source_suffix(
            row.get("title", ""),
            row.get("source", ""),
        )
        lower = original.lower()

        # 같은 자료에서 동일 키워드는 한 번만 셉니다.
        for label, variants in KEYWORD_PHRASES.items():
            if any(variant.lower() in lower for variant in variants):
                phrase_counter[label] += 1

        clean_text = keyword_text(row)
        source_tokens = {
            token.lower()
            for token in TOKEN_RE.findall(row.get("source", ""))
        }
        tokens = {
            token.lower()
            for token in TOKEN_RE.findall(clean_text)
            if (
                len(token) >= 2
                and token.lower() not in KEYWORD_NOISE
                and token.lower() not in source_tokens
                and not token.isdigit()
            )
        }
        fallback_counter.update(tokens)

    output: list[dict[str, Any]] = []
    used: set[str] = set()

    for word, count in phrase_counter.most_common():
        output.append({"word": word, "count": count})
        used.add(word.lower())
        if len(output) == 20:
            return output

    for word, count in fallback_counter.most_common():
        if word.lower() in used:
            continue
        output.append({"word": word, "count": count})
        used.add(word.lower())
        if len(output) == 20:
            break

    return output


def match_count(title: str, words: tuple[str, ...]) -> int:
    lower = title.lower()
    return sum(1 for word in words if word.lower() in lower)


def issue_rows(
    rows: list[dict[str, str]],
    days: int,
) -> list[dict[str, Any]]:
    current_start = TODAY - timedelta(days=days - 1)
    previous_start = current_start - timedelta(days=days)

    current = [
        row for row in rows
        if row_date(row) and row_date(row) >= current_start
    ]
    previous = [
        row for row in rows
        if row_date(row)
        and previous_start <= row_date(row) < current_start
    ]

    output: list[dict[str, Any]] = []
    for topic, words in TOPICS.items():
        matched = [
            row for row in current
            if match_count(strip_source_suffix(row["title"], row.get("source", "")), words) > 0
        ]
        if not matched:
            continue

        matched.sort(
            key=lambda row: (
                match_count(strip_source_suffix(row["title"], row.get("source", "")), words),
                row["date"],
            ),
            reverse=True,
        )
        previous_count = sum(
            1 for row in previous
            if match_count(strip_source_suffix(row["title"], row.get("source", "")), words) > 0
        )
        difference = len(matched) - previous_count

        if days == 365:
            trend = "최근 1년 누적"
        elif difference > 0:
            trend = f"직전 동일기간보다 {difference}건 증가"
        elif difference < 0:
            trend = f"직전 동일기간보다 {abs(difference)}건 감소"
        else:
            trend = "직전 동일기간과 동일"

        basis_rows = diversify_issue_rows(matched, limit=15)
        summary = build_issue_summary(topic, basis_rows)

        examples: list[dict[str, str]] = []
        for row in basis_rows[:4]:
            examples.append(
                {
                    "title": row.get("title", ""),
                    "url": row.get("url", ""),
                    "source": row.get("source", ""),
                    "date": row.get("date", ""),
                }
            )

        output.append(
            {
                "topic": topic,
                "count": len(matched),
                "trend_label": trend,
                "analyzed_count": len(basis_rows),
                "summary": summary,
                "examples": examples,
            }
        )

    output.sort(key=lambda row: row["count"], reverse=True)
    return output[:10]


def coverage(rows: list[dict[str, str]]) -> dict[str, Any]:
    yearly = period_rows(rows, 365)
    dates = [row_date(row) for row in yearly if row_date(row)]

    if not dates:
        return {
            "items": 0,
            "oldest": None,
            "newest": None,
            "days_covered": 0,
            "complete": False,
        }

    oldest = min(dates)
    newest = max(dates)
    span = (newest - oldest).days + 1

    return {
        "items": len(yearly),
        "oldest": oldest.isoformat(),
        "newest": newest.isoformat(),
        "days_covered": span,
        "complete": (
            len(yearly) >= 150
            and oldest <= TODAY - timedelta(days=330)
        ),
    }


def write_json(path: Path, payload: Any) -> None:
    path.write_text(
        json.dumps(payload, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )


def main() -> None:
    old_archive = load_json(ARCHIVE_PATH, [])
    if not isinstance(old_archive, list):
        old_archive = []

    current, current_status = run_jobs(current_jobs(), "최근수집")
    municipal_notices, municipal_status = collect_municipal_notices()
    maintenance_updates, maintenance_status = (
        collect_public_maintenance_updates()
    )
    combined = old_archive + current

    old_report = coverage(old_archive)
    state = load_json(STATE_PATH, {})
    need_backfill = (
        not state.get("complete")
        or not old_report.get("complete")
    )

    backfill_status: dict[str, str] = {}
    if need_backfill:
        historical, backfill_status = run_jobs(
            backfill_jobs(),
            "1년 역수집",
        )
        combined.extend(historical)

    archive = deduplicate(combined)

    # 기존 archive에 남아 있던 연구 사진·홍보물과 일반 법령 페이지도
    # 매 실행 때 다시 검사하여 정리합니다.
    quality_archive: list[dict[str, str]] = []
    for row in archive:
        category = clean(row.get("category", ""))
        title = clean(row.get("title", ""))
        reason = exclusion_reason(category, title)
        if reason:
            FILTER_COUNTS["기존자료 정리: " + reason] += 1
            continue
        quality_archive.append(row)

    archive = [
        row for row in quality_archive
        if row_date(row)
        and KEEP_START <= row_date(row) <= TODAY + timedelta(days=1)
    ]
    archive.sort(
        key=lambda row: (row.get("date", ""), row.get("source", "")),
        reverse=True,
    )

    report = coverage(archive)
    updated_at = NOW.strftime("%Y-%m-%d %H:%M KST")
    yearly = period_rows(archive, 365)

    official_recent = [
        row for row in period_rows(archive, 14)
        if row.get("source") in {"국토교통부", "서울특별시", "경기도"}
    ]

    # 세 공식 정책자료가 모두 0건이면 기존 정상 자료를 덮어쓰지 않습니다.
    current_official_count = sum(
        1 for row in current
        if row.get("source") in {"국토교통부", "서울특별시", "경기도"}
    )
    if current_official_count == 0 and not official_recent:
        raise RuntimeError(
            "국토부·서울시·경기도의 최근 공식자료를 한 건도 확인하지 못했습니다."
        )

    if report["complete"]:
        write_json(
            STATE_PATH,
            {
                "complete": True,
                "completed_at": NOW.isoformat(),
                "coverage": report,
            },
        )

    write_json(ARCHIVE_PATH, archive)
    write_json(
        LATEST_PATH,
        {
            "updated_at": updated_at,
            "coverage": report,
            "period_counts": {
                "weekly": category_counts(archive, 7),
                "monthly": category_counts(archive, 30),
                "yearly": category_counts(archive, 365),
            },
            "source_status": current_status,
            "backfill_status": backfill_status,
            "municipal_notices": municipal_notices,
            "municipal_status": municipal_status,
            "maintenance_updates": maintenance_updates,
            "maintenance_status": maintenance_status,
            "items": yearly[:200],
        },
    )
    write_json(
        KEYWORDS_PATH,
        {
            "updated_at": updated_at,
            "monthly": keyword_rows(archive, 30),
            "quarterly": keyword_rows(archive, 90),
            "yearly": keyword_rows(archive, 365),
        },
    )
    write_json(
        ISSUES_PATH,
        {
            "updated_at": updated_at,
            "coverage": report,
            "weekly": issue_rows(archive, 7),
            "monthly": issue_rows(archive, 30),
            "yearly": issue_rows(archive, 365),
        },
    )

    print("=== 최근 공식자료 ===")
    for source in ("국토교통부", "서울특별시", "경기도"):
        print(f"{source}: {current_status.get(source, '확인 불가')}")

    print("=== 공공지원 정비사업 추진사항 ===")
    print(f"최근 추진사항 {len(maintenance_updates)}건")
    for city in (
        "서울", "인천", "수원", "화성", "남양주", "고양",
        "성남", "평택", "과천", "광명", "광주"
    ):
        print(f"{city}: {maintenance_status.get(city, '확인 불가')}")

    print("=== 주요 도시계획 고시 ===")
    print(f"선택 도시 고시 {len(municipal_notices)}건")
    for city in (
        "서울", "인천", "수원", "화성", "남양주", "고양",
        "성남", "평택", "과천", "광명", "광주"
    ):
        print(f"{city}: {municipal_status.get(city, '확인 불가')}")

    print("=== 품질 필터 ===")
    if FILTER_COUNTS:
        for reason, count in FILTER_COUNTS.items():
            print(f"{reason}: {count}건 제외")
    else:
        print("제외된 자료 없음")

    print(
        "RESULT "
        f"items={report['items']} "
        f"oldest={report['oldest']} "
        f"newest={report['newest']} "
        f"days={report['days_covered']} "
        f"complete={report['complete']} "
        f"official14d={len(official_recent)}"
    )


if __name__ == "__main__":
    main()
