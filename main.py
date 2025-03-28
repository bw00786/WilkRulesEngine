import logging
import os
import json
from sqlalchemy import text
import asyncio
import asyncpg
import time
import pandas as pd
from pydantic import BaseModel
import openpyxl
from sqlalchemy import create_engine
from sqlalchemy.orm import sessionmaker
from sqlalchemy.ext.declarative import declarative_base
from sqlalchemy import inspect
from datetime import datetime
from typing import List, Dict, Any, Optional, Union
from contextlib import asynccontextmanager
from fastapi import FastAPI, UploadFile, File, HTTPException, Depends
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import FileResponse
from sqlalchemy.ext.asyncio import AsyncSession, create_async_engine
from sqlalchemy.orm import sessionmaker, declarative_base
from sqlalchemy import Column, Integer, String, JSON, select, UniqueConstraint
from pydantic import BaseModel, ValidationError, validator, Field
import uvicorn
from enum import Enum, auto
import networkx as nx
import matplotlib.pyplot as plt
from redis.asyncio import Redis
from redis.exceptions import RedisError
from dataclasses import dataclass  # Add this line
from collections import deque

# Configure logging
logging.basicConfig(level=logging.INFO, format="%(asctime)s - %(levelname)s - %(message)s")
logger = logging.getLogger(__name__)

# --------------------------
# Configuration
# --------------------------
DATABASE_URL = "postgresql+asyncpg://user:password@localhost:5433/rules_db"
REDIS_URL = "redis://localhost:6379/0"
CACHE_TTL = 300  # 5 minutes
MAX_POOL_SIZE = int(os.getenv('POOL_SIZE', 20))
MAX_OVERFLOW = int(os.getenv('MAX_OVERFLOW', 5))
DATABASE_PORT = int(os.getenv('DATABASE_PORT', 54321))


# Create SQLAlchemy async engine
engine = create_async_engine(
  DATABASE_URL,
  pool_size=MAX_POOL_SIZE,
  max_overflow=MAX_OVERFLOW
)

# Create an async session factory
AsyncSessionLocal = sessionmaker(engine, class_=AsyncSession, expire_on_commit=False)


# Define the Base for SQLAlchemy models
Base = declarative_base()

# --------------------------
# Redis Setup
# --------------------------
async def get_redis():
    redis = Redis.from_url(REDIS_URL, decode_responses=True)
    try:
        yield redis
    finally:
        await redis.close()

class RuleDependencyType(Enum):
    """Enum to represent different types of rule dependencies"""
    DIRECT = auto()
    CONTEXTUAL = auto()
    OPTIONAL = auto()
    CRITICAL = auto()

@dataclass
class RuleDependencyMetadata:
    """Comprehensive metadata for rule dependencies"""
    name: str
    context: str
    weight: float = 1.0
    execution_time: float = 0.0
    complexity: float = 0.0
    dependency_type: RuleDependencyType = RuleDependencyType.DIRECT
    last_executed: Optional[datetime] = None
    execution_count: int = 0
    failure_count: int = 0

    

class RuleDependencyGraph:
    def __init__(self):
        """
        Create a sophisticated rule dependency graph using NetworkX
        """
        self.graph = nx.DiGraph()
        self.rule_metadata: Dict[str, RuleDependencyMetadata] = {}

    def add_rule(self, rule: Dict[str, Any]):
        """
        Add a rule to the dependency graph with comprehensive metadata
        """
        rule_name = rule.get('name')
        rule_context = rule.get('context', 'default')
        
        # Create or update rule metadata
        metadata = RuleDependencyMetadata(
            name=rule_name,
            context=rule_context,
            weight=rule.get('priority', 1.0) / 10.0,  # Normalize priority
            complexity=self._calculate_rule_complexity(rule)
        )
        self.rule_metadata[rule_name] = metadata
        
        # Add node to graph
        self.graph.add_node(rule_name, metadata=metadata)

    def add_dependency(
        self, 
        source_rule: str, 
        target_rule: str, 
        dependency_type: RuleDependencyType = RuleDependencyType.DIRECT
    ):
        """
        Add a weighted, typed dependency between rules
        """
        if source_rule not in self.graph.nodes or target_rule not in self.graph.nodes:
            raise ValueError(f"Rules {source_rule} or {target_rule} not in graph")
        
        weight = self._calculate_dependency_weight(
            self.rule_metadata[source_rule], 
            self.rule_metadata[target_rule]
        )
        
        self.graph.add_edge(
            source_rule, 
            target_rule, 
            weight=weight, 
            type=dependency_type
        )

    def _calculate_rule_complexity(self, rule: Dict[str, Any]) -> float:
        """
        Calculate rule complexity based on conditions and actions
        """
        conditions = rule.get('conditions', {})
        actions = rule.get('actions', [])
        
        # Basic complexity calculation
        condition_complexity = self._count_nested_conditions(conditions)
        action_complexity = len(actions)
        
        return (condition_complexity * 0.6) + (action_complexity * 0.4)

    def _count_nested_conditions(self, conditions: Dict[str, Any]) -> int:
        """
        Recursively count nested conditions
        """
        if isinstance(conditions, dict):
            if 'and' in conditions or 'or' in conditions:
                return 1 + sum(
                    self._count_nested_conditions(cond) 
                    for cond in conditions.get('and', []) + conditions.get('or', [])
                )
            return 1
        return 0

    def _calculate_dependency_weight(
        self, 
        source_metadata: RuleDependencyMetadata, 
        target_metadata: RuleDependencyMetadata
    ) -> float:
        """
        Calculate dependency weight based on rule metadata
        """
        context_match = (source_metadata.context == target_metadata.context)
        
        return (
            source_metadata.weight * 
            target_metadata.weight * 
            (1.5 if context_match else 1.0)
        )

    def detect_cycles(self, max_depth: int = 10) -> List[List[str]]:
        """
        Detect cycles in the dependency graph with configurable depth
        """
        try:
            cycles = list(nx.simple_cycles(self.graph))
            return [cycle for cycle in cycles if len(cycle) <= max_depth]
        except nx.NetworkXNoCycle:
            return []

    def optimize_execution_order(self) -> List[str]:
        """
        Optimize rule execution order using topological sorting
        """
        try:
            return list(nx.topological_sort(self.graph))
        except nx.NetworkXUnfeasible:
            # Handle graphs with cycles
            return self._handle_cyclic_graph()

    def _handle_cyclic_graph(self) -> List[str]:
        """
        Handle graphs with cycles by breaking cycles strategically
        """
        cycles = self.detect_cycles()
        
        # Create a copy of the graph to manipulate
        working_graph = self.graph.copy()
        
        for cycle in cycles:
            # Break the cycle by removing the weakest dependency
            weakest_edge = min(
                ((u, v) for u, v in zip(cycle, cycle[1:] + [cycle[0]])),
                key=lambda edge: self.graph[edge[0]][edge[1]].get('weight', 1.0)
            )
            working_graph.remove_edge(*weakest_edge)
        
        return list(nx.topological_sort(working_graph))

    def visualize_dependency_graph(self, output_path: str = '/tmp/rule_dependency_graph.png'):
        """
        Generate a visual representation of the rule dependency graph
        """
        plt.figure(figsize=(12, 8))
        pos = nx.spring_layout(self.graph, k=0.5, iterations=50)
        
        # Draw nodes
        nx.draw_networkx_nodes(
            self.graph, 
            pos, 
            node_color='lightblue', 
            node_size=500
        )
        
        # Draw edges
        nx.draw_networkx_edges(
            self.graph, 
            pos, 
            edge_color='gray',
            arrows=True
        )
        
        # Draw labels
        nx.draw_networkx_labels(self.graph, pos, font_size=8)
        
        plt.title("Rule Dependency Graph")
        plt.axis('off')
        plt.tight_layout()
        plt.savefig(output_path)
        plt.close()
        
        return output_path

    def export_dependency_graph(self) -> Dict[str, Any]:
        """
        Export rule dependency graph as a structured JSON
        """
        graph_data = {
            'nodes': [],
            'edges': [],
            'metadata': {}
        }
        
        # Export nodes
        for node in self.graph.nodes():
            metadata = self.rule_metadata.get(node)
            graph_data['nodes'].append({
                'id': node,
                'context': metadata.context,
                'weight': metadata.weight,
                'complexity': metadata.complexity
            })
            
            graph_data['metadata'][node] = {
                'execution_time': metadata.execution_time,
                'execution_count': metadata.execution_count,
                'last_executed': metadata.last_executed.isoformat() if metadata.last_executed else None
            }
        
        # Export edges
        for source, target, data in self.graph.edges(data=True):
            graph_data['edges'].append({
                'source': source,
                'target': target,
                'weight': data.get('weight', 1.0),
                'type': data.get('type', 'DIRECT').name
            })
        
        return graph_data    

class EvaluateRulesRequest(BaseModel):
    context: str
    facts: Dict[str, Any]
    
    @validator('context')
    def validate_context(cls, v):
        if not v.strip():
            raise ValueError("Context cannot be empty")
        return v.lower()        

class ExcelRuleUploader:
    def __init__(self, db: AsyncSession):
        self.db = db
        self.logger = logging.getLogger(__name__)

    async def validate_excel_structure(self, file_path: str) -> List[Dict[str, Any]]:
        """
        Validate Excel file structure and convert to rules
        
        Expected Excel Columns:
         - context(str): Context
        - name (str): Rule name
        - priority (int): Rule priority
        - description (str): Rule description
        - conditions (json): Conditions in JSON format
        - actions (json): Actions in JSON format
        """
        try:
            # Read Excel file
            df = pd.read_excel(file_path)
            
            # Required columns
            required_columns = [
                'context','name', 'priority', 'description', 
                'conditions', 'actions'
            ]
            
            # Check if all required columns exist
            missing_columns = [col for col in required_columns if col not in df.columns]
            if missing_columns:
                raise ValueError(f"Missing columns: {', '.join(missing_columns)}")
            
            # Convert DataFrame to list of dictionaries
            rules = []
            for _, row in df.iterrows():
                try:
                    # Parse JSON strings for conditions and actions
                    conditions = json.loads(row['conditions']) if isinstance(row['conditions'], str) else row['conditions']
                    actions = json.loads(row['actions']) if isinstance(row['actions'], str) else row['actions']
                    
                    rule = {
                        'context': str(row['context']),
                        'name': str(row['name']),
                        'priority': int(row['priority']),
                        'description': str(row['description']),
                        'conditions': conditions,
                        'actions': actions
                    }
                    
                    # Validate rule structure
                    RuleCreate(**rule)
                    rules.append(rule)
                
                except (json.JSONDecodeError, ValidationError) as e:
                    self.logger.error(f"Invalid rule in row: {row}. Error: {str(e)}")
                    raise HTTPException(
                        status_code=400, 
                        detail=f"Invalid rule structure in row: {str(e)}"
                    )
            
            return rules
        
        except Exception as e:
            self.logger.error(f"Excel file processing error: {str(e)}")
            raise HTTPException(
                status_code=400, 
                detail=f"Excel file processing failed: {str(e)}"
            )
        finally:
            logger.info("removeing files")

    async def validate_excel_structure(self, file_path: str) -> List[Dict[str, Any]]:
            """
                Validate Excel file structure and convert to rules
        
                 Expected Excel Columns:
                 - context (str): context of rules
                 - name (str): Rule name
                 - priority (int): Rule priority
                 - description (str): Rule description
                 - conditions (json): Conditions in JSON format
                 - actions (json): Actions in JSON format
            """
            try:
                # Read Excel file
                df = pd.read_excel(file_path)
            
                # Required columns
                required_columns = [
                  'context', 'name',  'priority', 'description', 
                  'conditions', 'actions'
                ]
            
                # Check if all required columns exist
                missing_columns = [col for col in required_columns if col not in df.columns]
                if missing_columns:
                   raise ValueError(f"Missing columns: {', '.join(missing_columns)}")
            
                # Convert DataFrame to list of dictionaries
                rules = []
                for _, row in df.iterrows():
                    try:
                       # Parse JSON strings for conditions and actions
                       conditions = json.loads(row['conditions']) if isinstance(row['conditions'], str) else row['conditions']
                       actions = json.loads(row['actions']) if isinstance(row['actions'], str) else row['actions']
                    
                       rule = {
                           'context': str(row['context']),
                           'name': str(row['name']),
                           'priority': int(row['priority']),
                           'description': str(row['description']),
                           'conditions': conditions,
                           'actions': actions
                        }
                    
                        # Validate rule structure
                       RuleCreate(**rule)
                       rules.append(rule)
                
                    except (json.JSONDecodeError, ValidationError) as e:
                       self.logger.error(f"Invalid rule in row: {row}. Error: {str(e)}")
                       raise HTTPException(
                          status_code=400, 
                          detail=f"Invalid rule structure in row: {str(e)}"
                       )
            
                    return rules
        
            except Exception as e:
                self.logger.error(f"Excel file processing error: {str(e)}")
                raise HTTPException(
                          status_code=400, 
                          detail=f"Excel file processing failed: {str(e)}"
                )
            finally:
                         # Clean up temporary file if it exists
                if os.path.exists(file_path):
                   os.remove(file_path)
                if os.path.exists(file_path):
                   os.remove(file_path)        

# --------------------------
# Pydantic Models
# --------------------------
class ContextualRuleEvaluator:
    def __init__(self, db: AsyncSession):
        self.db = db
        self.dependency_graph = RuleDependencyGraph()
        self.logger = logging.getLogger(__name__)

    async def prepare_rule_graph(self, rules: List[Dict[str, Any]], context: str):
        """
        Prepare a comprehensive rule dependency graph and return execution order
    
         Args:
        rules: List of rule dictionaries
        context: Context for the rules
    
         Returns:
        List[str]: Optimized execution order of rule names
    
         Raises:
            ValueError: If cyclic dependencies are detected
        """
         # Reset graph for new context
        self.dependency_graph = RuleDependencyGraph()
    
        # Add rules to graph
        for rule in rules:
            self.dependency_graph.add_rule(rule)
    
        # Analyze and add dependencies
        for rule in rules:
           await self._analyze_rule_dependencies(rule, rules)
    
        # Detect cycles
        cycles = self.dependency_graph.detect_cycles()
        if cycles:
          self.logger.warning(f"Detected dependency cycles: {cycles}")
          raise ValueError(f"Cyclic dependencies detected in rules: {cycles}")
    
        # Get optimized execution order
        return self.dependency_graph.optimize_execution_order()

    async def _analyze_rule_dependencies(self, rule: Dict[str, Any], all_rules: List[Dict[str, Any]]):
        """
        Analyze and add rule dependencies dynamically
        """
        def _find_referenced_rules(conditions: Dict[str, Any]):
            """Recursively find referenced rules"""
            referenced = []
            if isinstance(conditions, dict):
                if 'refRule' in conditions:
                    referenced.append(conditions['refRule'])
                
                for value in conditions.values():
                    if isinstance(value, (dict, list)):
                        referenced.extend(_find_referenced_rules(value))
            
            elif isinstance(conditions, list):
                for item in conditions:
                    referenced.extend(_find_referenced_rules(item))
            
            return referenced

        # Find referenced rules in conditions
        referenced_rules = _find_referenced_rules(rule.get('conditions', {}))
        
        for ref_rule_name in referenced_rules:
            # Find the referenced rule
            ref_rule = next((r for r in all_rules if r['name'] == ref_rule_name), None)
            
            if ref_rule:
                dependency_type = (
                    RuleDependencyType.CRITICAL if ref_rule.get('priority', 0) > 7 
                    else RuleDependencyType.OPTIONAL
                )
                
                try:
                    self.dependency_graph.add_dependency(
                        rule['name'], 
                        ref_rule_name, 
                        dependency_type
                    )
                except ValueError as e:
                    self.logger.warning(f"Dependency error: {e}")

    async def evaluate_rules(
        self, 
        rules: List[Dict[str, Any]], 
        facts: Dict[str, Any], 
        context: str
    ):
        """
        Evaluate rules with advanced dependency management
        """
        # Prepare rule graph and get optimal execution order
        execution_order = await self.prepare_rule_graph(rules, context)
        
        # Track rule evaluation results
        evaluation_results = []
        
        # Parallel rule evaluation with dependency awareness
        async def evaluate_rule_with_tracking(rule):
            start_time = datetime.now()
            try:
                # Existing rule evaluation logic
                result = await self._evaluate_rule(rule, facts)
                
                # Update rule metadata
                metadata = self.dependency_graph.rule_metadata.get(rule['name'])
                if metadata:
                    metadata.execution_time = (datetime.now() - start_time).total_seconds()
                    metadata.execution_count += 1
                    metadata.last_executed = datetime.now()
                
                return result
            except Exception as e:
                # Track failures
                metadata = self.dependency_graph.rule_metadata.get(rule['name'])
                if metadata:
                    metadata.failure_count += 1
                
                self.logger.error(f"Rule {rule['name']} evaluation failed: {e}")
                return None

        # Find rules in execution order
        ordered_rules = [
            rule for rule in rules 
            if rule['name'] in execution_order
        ]
        
        # Execute rules
        evaluation_results = await asyncio.gather(
            *[evaluate_rule_with_tracking(rule) for rule in ordered_rules]
        )
        
        # Optional: Visualize rule dependency graph
        graph_visualization_path = self.dependency_graph.visualize_dependency_graph()
        
        return {
            'results': evaluation_results,
            'execution_order': execution_order,
            'dependency_graph': self.dependency_graph.export_dependency_graph(),
            'graph_visualization': graph_visualization_path
        }

    async def _evaluate_rule(self, rule: Dict[str, Any], facts: Dict[str, Any]) -> Dict[str, Any]:
        """
        Evaluate a single rule against facts and return detailed results
    
        Returns:
        {
            "rule_name": str,
            "conditions_met": bool,
            "conditions_evaluated": List[Dict],
            "actions": List[Dict],
            "matched_conditions": List[Dict]
        }
        """

        start_time = time.time()  # Initialize timer
        try:

            # Get all rules for context (needed for rule references)
            all_rules = [rule]  # In your case, just this single rule
            # Evaluate conditions
            conditions_met = await evaluate_conditions (
              rule['conditions'],
              facts,
              rule.get('context', 'default'),
              all_rules
            )

            # Get which specific conditions matched
            matched_conditions = self._find_matched_conditions(
               rule['conditions'],
               facts,
               all_rules
            )
        
            return {
               "rule_name": rule['name'],
               "conditions_met": conditions_met,
               "conditions_evaluated": rule['conditions'],
               "actions": rule['actions'] if conditions_met else [],
               "matched_conditions": matched_conditions,
               "execution_time": time.time() - start_time
            }
        
        except Exception as e:
             logger.error(f"Error evaluating rule {rule.get('name')}: {str(e)}")
             return {
                "rule_name": rule.get('name', 'unknown'),
                "error": str(e),
                "conditions_met": False,
                "execution_time": time.time() - start_time
             }
    def _find_matched_conditions(self, conditions: Dict, facts: Dict, all_rules: List) -> List[Dict]:
        """Recursively find which conditions matched"""
        matched = []
    
        if not isinstance(conditions, dict):
         return matched
        
        if 'and' in conditions:
          for cond in conditions['and']:
            if self._condition_matches(cond, facts, all_rules):
                matched.append(cond)
                
        elif 'or' in conditions:
           for cond in conditions['or']:
            if self._condition_matches(cond, facts, all_rules):
                matched.append(cond)
                
        return matched   

    def _condition_matches(self, condition: Dict, facts: Dict, all_rules: List) -> bool:
        """Check if a single condition matches facts"""
        if 'refRule' in condition:
           return self._handle_rule_reference(condition['refRule'], facts, all_rules)
        
        for field, condition_def in condition.items():
            if not isinstance(condition_def, dict):
                continue
            
            op = condition_def.get('operator')
            val = condition_def.get('value')
            fact_val = facts.get(field)
        
            try:
               if op == "==": return fact_val == val
               elif op == "!=": return fact_val != val
               elif op == ">=": return float(fact_val) >= float(val)
               elif op == "<=": return float(fact_val) <= float(val)
               elif op == ">": return float(fact_val) > float(val)
               elif op == "<": return float(fact_val) < float(val)
               elif op == "in": return fact_val in val if isinstance(val, (list, tuple)) else False
               elif op == "not_in": return fact_val not in val if isinstance(val, (list, tuple)) else True
            except (TypeError, ValueError):
               return False 
            
    def _handle_rule_reference(self, rule_name: str, facts: Dict, all_rules: List) -> bool:
        """Handle references to other rules"""
        ref_rule = next((r for r in all_rules if r['name'] == rule_name), None)
        if not ref_rule:
            return False
        
        return self._evaluate_rule(ref_rule, facts)['conditions_met']        

    def _get_matched_conditions(self, conditions: Dict, facts: Dict) -> List[Dict]:
        """Helper to identify which specific conditions matched"""
        matched = []
    
        if 'and' in conditions:
            for cond in conditions['and']:
                if self._condition_matches(cond, facts):
                   matched.append(cond)
                
        elif 'or' in conditions:
            for cond in conditions['or']:
                if self._condition_matches(cond, facts):
                    matched.append(cond)
                
        return matched
  

# Updated Rule Model to support enhanced metadata
class EnhancedRuleModel(BaseModel):
    name: str
    context: str
    priority: int = 5
    conditions: Dict[str, Any]
    actions: List[Dict[str, Any]]
    metadata: Dict[str, Any] = Field(default_factory=dict)    

class Condition(BaseModel):
    operator: str
    value: Any

class Action(BaseModel):
    type: str
    parameters: Optional[Dict[str, Any]] = None
    key: Optional[str] = None
    value: Optional[Any] = None

class RuleCreate(BaseModel):
    context: str = Field(default="default")
    name: str
    priority: int = Field(5, ge=1, le=10)
    description: str = Field(default="No description provided")
    conditions: Dict[str, Any]
    actions: List[Action]

    @validator('actions')
    def validate_actions(cls, v):
        for action in v:
            if action.parameters is None and (action.key is None or action.value is None):
                raise ValueError("Action must have either parameters or key/value pair")
        return v


# --------------------------
# Database Models
# --------------------------
class RuleModel(Base):
    __tablename__ = "rules3456716"
    id = Column(Integer, primary_key=True, index=True)
    context = Column(String, index=True) 
    name = Column(String, index=True)
    priority = Column(Integer, default=5, nullable=False)
    description = Column(String,  nullable=True)
    conditions = Column(JSON, nullable=False)
    actions = Column(JSON, nullable=False)
    
   ## __table_args__ = (UniqueConstraint('context', 'name',  name='uq_rule_name_context'),)

# --------------------------
# Cache Management
# --------------------------
class RuleCache:
    def __init__(self, redis: Redis):
        self.redis = redis
        self.lock = asyncio.Lock()
        self.cache_key = "rules:all"
        self.timestamp_key = "rules:last_updated"

    async def get_rules(self) -> List[Dict]:
        """Retrieve rules from Redis cache"""
        try:
            cached_data = await self.redis.get(self.cache_key)
            return json.loads(cached_data) if cached_data else []
        except RedisError as e:
            logger.error(f"Redis error: {str(e)}")
            return []

    async def is_cache_stale(self) -> bool:
        """Check if cache needs refresh"""
        try:
            last_update = await self.redis.get(self.timestamp_key)
            if not last_update:
                return True
            last_db_update = datetime.fromisoformat(last_update)
            return (datetime.now() - last_db_update).seconds > CACHE_TTL
        except (RedisError, ValueError):
            return True

    async def refresh(self, db: AsyncSession):
        """Refresh cache from database"""
        async with self.lock:
            try:
                result = await db.execute(
                    select(RuleModel).order_by(RuleModel.priority.asc())
                )
                rules = result.scalars().all()
                
                serialized_rules = json.dumps([
                    {
                        "id": rule.id,
                        "context": rule.context,
                        "name": rule.name,
                        "priority": rule.priority,
                        "description": rule.description,  # Fixed typo here
                        "conditions": rule.conditions,
                        "actions": rule.actions
                    } for rule in rules
                ])
                
                async with self.redis.pipeline() as pipe:
                    await pipe.set(self.cache_key, serialized_rules)
                    await pipe.set(self.timestamp_key, datetime.now().isoformat())
                    await pipe.execute()
                
                logger.info(f"Refreshed Redis cache with {len(rules)} rules")
            except Exception as e:
                logger.error(f"Cache refresh failed: {str(e)}")
                raise

# --------------------------
# FastAPI Setup
# --------------------------
@asynccontextmanager
async def lifespan(app: FastAPI):
    async with engine.begin() as conn:
        # Check if tables exist first
        logger.info("chaecking for table existence")
        if not await conn.run_sync(lambda sync_conn: inspect(sync_conn).has_table("rules3456716")):
            await conn.run_sync(Base.metadata.create_all)
    yield
    
    # Rest of your lifespan code...
    redis = Redis.from_url(REDIS_URL, decode_responses=True)
    rule_cache = RuleCache(redis)
    async with AsyncSessionLocal() as db:
        await rule_cache.refresh(db)
    yield
    await redis.close()


def check_and_update_columns(conn):
    # CORRECTED TABLE NAME TO MATCH MODEL
    table_name = "rules3456716"
    
    inspector = inspect(conn)
    
    # Check if table exists first
    if not inspector.has_table(table_name):
        return
        
    columns = inspector.get_columns(table_name)
    
    # Check for priority column
    if not any(col['name'] == 'priority' for col in columns):
        # CORRECTED TABLE NAME IN SQL
        conn.execute(text(
            f"ALTER TABLE {table_name} ADD COLUMN priority INTEGER NOT NULL DEFAULT 5"
        ))
        conn.commit()

app = FastAPI(lifespan=lifespan)

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# --------------------------
# Dependency Injection
# --------------------------
async def get_db():
    async with AsyncSessionLocal() as session:
        try:
            yield session
        finally:
            await session.close()

async def get_cache(redis: Redis = Depends(get_redis)) -> RuleCache:
    return RuleCache(redis)

# --------------------------
# Rule Evaluation Logic (FIXED)
# --------------------------
async def evaluate_condition(
    condition: Dict[str, Any],
    facts: Dict[str, Any],
    context: str,
    all_rules: List[Dict],
    depth: int = 0
) -> bool:
    if depth > 10:
        raise RecursionError("Maximum condition nesting depth exceeded")

    if "refRule" in condition:
        rule_name = condition["refRule"]
        referenced_rule = next((r for r in all_rules if r["name"] == rule_name), None)
        if referenced_rule:
            return await evaluate_conditions(
                referenced_rule["conditions"],
                facts,
                context,
                all_rules,
                depth + 1
            )
        return False

    if "and" in condition:
        results = await asyncio.gather(*[
            evaluate_conditions(c, facts, context, all_rules, depth + 1)
            for c in condition["and"]
        ])
        return all(results)

    if "or" in condition:
        results = await asyncio.gather(*[
            evaluate_conditions(c, facts, context, all_rules, depth + 1)
            for c in condition["or"]
        ])
        return any(results)

    for field, condition_def in condition.items():
        if not isinstance(condition_def, dict):
            # Skip non-dict condition definitions
            continue
            
        try:
            op = condition_def.get("operator")
            val = condition_def.get("value")
            
            if op is None or val is None:
                continue
        except (KeyError, AttributeError):
            continue

        # Get fact value and handle missing facts
        fact_val = facts.get(field)
        
        # Type safety for comparisons
        try:
            if op == "==":
                return fact_val == val
            elif op == "!=":
                return fact_val != val
            elif op == ">=":
                # Type check for comparison operators
                if fact_val is None or val is None:
                    return False
                return float(fact_val) >= float(val)
            elif op == "<=":
                if fact_val is None or val is None:
                    return False
                return float(fact_val) <= float(val)
            elif op == ">":
                if fact_val is None or val is None:
                    return False
                return float(fact_val) > float(val)
            elif op == "<":
                if fact_val is None or val is None:
                    return False
                return float(fact_val) < float(val)
            elif op == "in":
                if fact_val is None or not isinstance(val, (list, tuple)):
                    return False
                return fact_val in val
            elif op == "not_in":
                if fact_val is None or not isinstance(val, (list, tuple)):
                    return False
                return fact_val not in val
        except (TypeError, ValueError) as e:
            # Log the error but don't crash
            logger.warning(f"Type error in comparison: {fact_val} {op} {val}. Error: {str(e)}")
            return False

    return False

async def evaluate_conditions(
    conditions: Dict[str, Any],
    facts: Dict[str, Any],
    context: str,
    all_rules: List[Dict],
    depth: int = 0
) -> bool:
    return await evaluate_condition(conditions, facts, context, all_rules, depth)

# --------------------------
# API Endpoints
# --------------------------
@app.post("/upload_rules/")
async def upload_rules(
    file: UploadFile = File(...),
    db: AsyncSession = Depends(get_db),
    cache: RuleCache = Depends(get_cache)
):
    """
    Upload rules via JSON or Excel file with enhanced validation and cycle detection.
    
    Args:
        file: Uploaded file (Excel or JSON)
        db: Database session
        cache: Rule cache instance
        
    Returns:
        dict: Success message with count of uploaded rules
        
    Raises:
        HTTPException: For validation errors or processing failures
    """
    try:
        # Determine file type
        filename = file.filename.lower()
        logger.info(f"Processing uploaded file: {filename}")
        
        # Create temporary file
        temp_path = f"/tmp/{filename}"
        with open(temp_path, "wb") as buffer:
            buffer.write(await file.read())
        
        # Process based on file extension
        uploader = ExcelRuleUploader(db)
        
        if filename.endswith(('.xlsx', '.xls')):
            rules_data = await uploader.validate_excel_structure(temp_path)
        elif filename.endswith('.json'):
            with open(temp_path, 'r') as f:
                rules_data = json.load(f)
                if not isinstance(rules_data, (list, dict)):
                    raise HTTPException(
                        status_code=400,
                        detail="JSON must be an array of rules or a single rule object"
                    )
        else:
            raise HTTPException(
                status_code=400, 
                detail="Unsupported file type. Use .xlsx, .xls, or .json"
            )
        
        # Clean up temporary file
        if os.path.exists(temp_path):
            os.remove(temp_path)
        
        # Convert single rule to list format if needed
        if isinstance(rules_data, dict):
            rules_data = [rules_data]
            
        if not rules_data:
            raise HTTPException(
                status_code=400,
                detail="No valid rules found in uploaded file"
            )
        
        # Validate all rules first
        evaluator = ContextualRuleEvaluator(db)
        context = rules_data[0].get('context', 'default') if rules_data else 'default'
        
        # Only check for cycles if multiple rules exist
        if len(rules_data) > 1:
            try:
                await evaluator.prepare_rule_graph(rules_data, context)
                logger.debug("No cyclic dependencies detected")
            except ValueError as e:
                if "Cyclic dependencies" in str(e):
                    raise HTTPException(
                        status_code=400,
                        detail=f"Rule validation failed: {str(e)}"
                    )
                raise
        
        # Validate each rule structure
        valid_rules = []
        for rule_data in rules_data:
            try:
                # Handle missing description
                rule_data.setdefault('description', '')
                
                # Convert key/value to parameters if needed
                if 'actions' in rule_data:
                    for action in rule_data['actions']:
                        if 'key' in action and 'value' in action:
                            action['parameters'] = {
                                'key': action.pop('key'),
                                'value': action.pop('value')
                            }
                
                valid_rules.append(RuleCreate(**rule_data))
                
            except ValidationError as e:
                error_details = []
                for err in e.errors():
                    loc = "->".join(str(x) for x in err['loc'])
                    error_details.append(f"{loc}: {err['msg']}")
                
                raise HTTPException(
                    status_code=422,
                    detail={
                        "message": "Rule validation failed",
                        "errors": error_details,
                        "offending_rule": rule_data
                    }
                )
        
        # Process in transaction
        try:
            async with db.begin():
                new_rule_count = 0
                for rule in valid_rules:
                    # Check for existing rule
                    existing = await db.execute(
                        select(RuleModel).where(
                            (RuleModel.name == rule.name) & 
                            (RuleModel.context == rule.context)
                        )
                    )
                    if existing.scalar():
                        await db.rollback()
                        raise HTTPException(
                            status_code=400,
                            detail=f"Rule '{rule.name}' in context '{rule.context}' already exists"
                        )
                    
                    # Add new rule
                    db.add(RuleModel(
                        context=rule.context,
                        name=rule.name,
                        priority=rule.priority,
                        description=rule.description,
                        conditions=rule.conditions,
                        actions=[action.dict() for action in rule.actions]
                    ))
                    new_rule_count += 1
                
                await db.commit()
                logger.info(f"Successfully added {new_rule_count} new rules")
            
            # Refresh cache with new independent session
            async with AsyncSessionLocal() as refresh_db:
                await cache.refresh(refresh_db)
            
            return {
                "message": f"Successfully processed {len(valid_rules)} rules",
                "new_rules_added": new_rule_count,
                "context": context
            }
            
        except Exception as e:
            await db.rollback()
            logger.error(f"Database error during rule upload: {str(e)}", exc_info=True)
            raise HTTPException(
                status_code=500,
                detail="Failed to save rules to database"
            )
            
    except HTTPException:
        # Re-raise existing HTTP exceptions
        raise
        
    except json.JSONDecodeError:
        raise HTTPException(
            status_code=400,
            detail="Invalid JSON format"
        )
        
    except Exception as e:
        logger.error(f"Unexpected error during rule upload: {str(e)}", exc_info=True)
        raise HTTPException(
            status_code=500,
            detail="An unexpected error occurred during rule upload"
        )

# Sample Excel Template Generation Endpoint
@app.get("/rule_upload_template")
async def generate_rule_upload_template():
    """
    Generate an Excel template for rule uploads
    """
    # Create a sample DataFrame with expected columns
    sample_data = pd.DataFrame([
        {
            'name': 'Sample Rule',
            'priority': 5,
            'description': 'A sample rule for demonstration',
            'conditions': json.dumps({
                'and': [
                    {'participant_status': {'operator': '==', 'value': 'Active'}},
                    {'age': {'operator': '>=', 'value': 73}}
                ]
            }),
            'actions': json.dumps([
                {
                    'type': 'calculate_rmd',
                    'target': 'system',
                    'parameters': {
                        'rmd_type': 'initial_rmd_73_2025'
                    }
                }
            ])
        }
    ])
    
    # Generate Excel file
    output_path = '/tmp/rule_upload_template.xlsx'
    sample_data.to_excel(output_path, index=False)
    
    # Return file for download
    return FileResponse(
        output_path, 
        media_type='application/vnd.openxmlformats-officedocument.spreadsheetml.sheet',
        filename='rule_upload_template.xlsx'
    )    
class evaluate_rules(BaseModel):
    context: str
    facts: Dict[str, Any]

@app.post("/evaluate_rules/")
async def evaluate_rules(
    request: evaluate_rules,
    db: AsyncSession = Depends(get_db),
    cache: RuleCache = Depends(get_cache)
):
    """
    Evaluate rules within a specific context, prioritizing cache retrieval
    """
    logger.info("evaluating rules")
    try:
        # Extract context and facts from the request
        context = request.context
        facts = request.facts
        logger.info(f"Here is context: {context}")
        logger.info(f"Here are facts: {facts}")
        
        # Retrieve rules from cache
        logger.info("Attempting to retrieve rules from cache")
        cached_rules = await cache.get_rules()
        # Filter rules for the specified context
        context_rules = [
            rule for rule in cached_rules 
            if rule.get('context') == context
        ]
        
        # If no rules in cache, check database and refresh cache
        if not context_rules:
            if await cache.is_cache_stale():
                # Refresh cache from database
                logger.info("refreshing cache from database")
                async with AsyncSessionLocal() as refresh_db:
                    await cache.refresh(refresh_db)
                    
                
                # Retry getting rules from cache
                logger.info("Gertings rules from cache)")
                cached_rules = await cache.get_rules()
                context_rules = [
                    rule for rule in cached_rules 
                    if rule.get('context') == context
                ]
            
            # If still no rules, raise exception
            if not context_rules:
                raise HTTPException(
                    status_code=404, 
                    detail=f"No rules found for context: {context}"
                )
        
       # Initialize evaluator
        evaluator = ContextualRuleEvaluator(db)
        
        # This is where ordered_rules comes from:
        execution_order = await evaluator.prepare_rule_graph(context_rules, context)
        
        # Create ordered_rules list based on execution_order
        ordered_rules = [rule for rule in context_rules if rule['name'] in execution_order]
        
        # This is where evaluation_results comes from:
        evaluation_results = await asyncio.gather(
            *[evaluator._evaluate_rule(rule, facts) for rule in ordered_rules]
        )
        
        
        return {
        "context": context,
        "input_facts": facts,
        "evaluation_results": [
            {
                "rule": result['rule_name'],
                "priority": rule['priority'],
                "conditions_met": result['conditions_met'],
                "actions_triggered": result.get('actions', []),
                "conditions_evaluated": result.get('conditions_evaluated', {}),
                "matched_conditions": result.get('matched_conditions', []),
                "execution_time_ms": round(result.get('execution_time', 0) * 1000, 2),
                "error": result.get('error')  # Include any errors
            }
            for rule, result in zip(ordered_rules, evaluation_results)
        ],
        "execution_order": execution_order,
        "dependency_graph": evaluator.dependency_graph.export_dependency_graph()
    }
    
    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Evaluation error: {str(e)}", exc_info=True)
        raise HTTPException(status_code=500, detail=str(e))
    
@app.post("/evaluate/")
async def evaluate_facts(
    facts: Dict[str, Any],
    context: str,
    cache: RuleCache = Depends(get_cache)
):
    try:
        # Get rules from Redis cache
        rules = await cache.get_rules()
        
        # Log received facts for debugging
        logger.info(f"Evaluating facts: {json.dumps(facts)}")
        
        # Fallback to database if cache is empty
        if not rules and await cache.is_cache_stale():
            async with AsyncSessionLocal() as db:
                await cache.refresh(db)
            rules = await cache.get_rules()

        results = []
        for rule in rules:
            try:
                if await evaluate_conditions(rule["conditions"], facts, context, rules):
                    results.append({
                        "context": rule["context"],
                        "rule_name": rule["name"], 
                        "priority": rule["priority"],
                        "actions": rule["actions"]
                    })
            except Exception as rule_error:
                logger.error(f"Error evaluating rule {rule.get('name')}: {str(rule_error)}")
                # Continue with other rules
                
        return {"matches": results}
    
    except Exception as e:
        logger.error(f"Evaluation error: {str(e)}", exc_info=True)
        raise HTTPException(status_code=500, detail="Evaluation failed")

# --------------------------
# Main Entry Point
# --------------------------
if __name__ == "__main__":
    uvicorn.run(
        app,
        host="0.0.0.0",
        port=8000,
        loop="uvloop",
        timeout_keep_alive=30
    )