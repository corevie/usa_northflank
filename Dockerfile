# Cloudflare IP 优选工具 - 容器镜像
# main.py 内部通过 subprocess 调用 curl，因此镜像内必须包含 curl
FROM python:3.12-slim

ENV PYTHONUNBUFFERED=1 \
    PYTHONDONTWRITEBYTECODE=1 \
    TZ=Asia/Shanghai

RUN apt-get update \
    && apt-get install -y --no-install-recommends curl ca-certificates tzdata \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /app

COPY requirements.txt /app/requirements.txt
RUN pip install --no-cache-dir -r /app/requirements.txt

COPY main.py /app/main.py
# config.json 已随镜像打入，请保持镜像私有，勿公开分发
COPY config.json /app/config.json

# 单次执行语义：由外部调度器（GitHub Actions schedule / Northflank Cron Job）触发
CMD ["python", "main.py"]
