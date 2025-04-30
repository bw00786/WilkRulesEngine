# WilkRulesEngine
# Rules Engine API

A high-performance rules engine built with FastAPI, PostgreSQL, and Redis. Evaluates complex business rules using the Rete algorithm, with audit logging and conflict resolution.

[![FastAPI](https://img.shields.io/badge/FastAPI-009688?style=flat&logo=fastapi)](https://fastapi.tiangolo.com)
[![Rete Algorithm](https://img.shields.io/badge/Rete-Algorithm-blue)](https://en.wikipedia.org/wiki/Rete_algorithm)

## Features

- 📊 **Excel/JSON Rule Uploads** - Bulk import rules with validation
- ⚡ **Rete Algorithm** - Efficient pattern matching for complex rule sets
- 🔗 **Rule Dependencies** - Context-aware execution order optimization
- 🛡️ **Conflict Resolution** - Priority-based action resolution
- 🔍 **Immutable Audit Logs** - Merkle tree-backed audit trails
- 📈 **Real-time Metrics** - Execution reports and dependency graphs

## Getting Started

### Prerequisites

- Docker & Docker Compose
- Python 3.9+
- PostgreSQL 14+ & Redis 6+

### Installation

1. **Clone Repository**
   ```bash
   git clone https://github.com/yourusername/rules-engine.git
   cd rules-engine

Start Databases

bash
docker-compose up -d postgres redis
Install Dependencies

bash
pip install -r requirements.txt
Run Migrations

bash
python -m alembic upgrade head
Start Server

bash
uvicorn main:app --reload --port 8000
API Endpoints
Method	Endpoint	Description
POST	/evaluate_rules/	Evaluate facts against rules
POST	/upload_rules/	Upload rules via Excel/JSON
GET	/rules/upload-reports	Get recent upload reports
POST	/validate_rules/	Validate rules without saving to DB
Example Usage
Evaluate Rules
bash
curl -X POST "http://localhost:8000/evaluate_rules/" \
-H "Content-Type: application/json" \
-d '{
  "context": "rmd",
  "facts": {
    "account_type": "IRA",
    "balance": 150000,
    "owner_age": 75,
    "distribution_year": 2023
  }
}'
Upload Rules (Excel)
bash
curl -X POST "http://localhost:8000/upload_rules/" \
-F "file=@/path/to/rules.xlsx" \
-F "sample_facts={\"age\":72}"
Audit System
Diagram
Code






### Development
**Environment Setup**

env
DATABASE_URL="postgresql+asyncpg://user:password@localhost:5433/rules_db"
REDIS_URL="redis://localhost:6379/0"
API Documentation
Access interactive docs at http://localhost:8000/docs

**Run Tests**

bash
pytest -v tests/
Architecture
python
class RuleEngine:
    def __init__(self):
        self.rete_network = ReteNetwork()
        self.validator = RuleValidator()
        self.auditor = AuditLogger()
        
    async def evaluate(self, facts: dict):
        matched = self.rete_network.process(facts)
        resolved = ConflictResolver.resolve(matched)
        self.auditor.log(resolved)
        return resolved
**License**
MIT License - See LICENSE


